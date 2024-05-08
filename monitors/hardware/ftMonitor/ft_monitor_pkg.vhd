-------------------------------------------------------------------------------
-- Project    : R2U2 (Realizable Responsive Unobtrusive Unit)
-------------------------------------------------------------------------------
-- File       : ft_monitor_pkg.vhd
-------------------------------------------------------------------------------
-- Description:  Package for future time monitor constants and components.                    
------------------------------------------------------------------------------- 

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.cevLib_unsigned_pkg.all;
use work.math_pkg.all;
use work.log_input_pkg.all;

package ft_monitor_pkg is
  subtype  operator_t is std_logic_vector(5-1 downto 0);
  --------------------------------------------------------------------
  --                          CONSTANTS                             --
  --------------------------------------------------------------------
  constant ROM_LEN             : integer := 64;  -- number of rom entries
  constant DATA_MEMORY_LEN     : integer := ROM_LEN;
  constant INTERVAL_MEMORY_LEN : integer := 64;
  constant TIMESTAMP_WIDTH     : integer := 16;
  constant COMMAND_WIDTH       : integer := 40;  -- width of ft_monitor-instruction
  constant m_DATA_WIDTH : integer := TIMESTAMP_WIDTH;
  constant t_pre_DATA_WIDTH : integer := TIMESTAMP_WIDTH;

  constant MEMBUS_ADDR_WIDTH   : integer := max(log2c(ROM_LEN), log2c(INTERVAL_MEMORY_LEN));
  constant MEMBUS_DATA_WIDTH   : integer := max(2*TIMESTAMP_WIDTH, COMMAND_WIDTH);
  constant SR_DATA_WIDTH : integer := 2*TIMESTAMP_WIDTH + 1;

  constant NUMBER_OF_QUEUES         : integer := ROM_LEN; --maximum instruction
  constant NUMBER_OF_QUEUE_ELEMENTS : integer := 2048;
  constant QUEUE_SIZE : integer := 32;
  constant DATA_QUEUE_SIZE : integer := NUMBER_OF_QUEUES*QUEUE_SIZE;

  -- Operators
  constant OP_LOAD               : operator_t := "11100";
  constant OP_START              : operator_t := "01011";
  constant OP_END                : operator_t := "01100";
  constant OP_FT_NOT             : operator_t := "10100";
  constant OP_FT_AND             : operator_t := "10101";
  constant OP_FT_BOXBOX          : operator_t := "10110";
  constant OP_FT_BOXDOT          : operator_t := "10111";
  constant OP_FT_DIAMONDDIAMOND  : operator_t := "11000";
  constant OP_FT_DIAMONDDOT      : operator_t := "11001";
  constant OP_FT_UNTIL           : operator_t := "11010";
  constant OP_FT_IMPLICIT        : operator_t := "11011";
  constant OP_END_SEQUENCE       : operator_t := "11111";

  type sr_t is record
    m        : std_logic_vector(m_DATA_WIDTH-1 downto 0);
    t_pre    : std_logic_vector(t_pre_DATA_WIDTH-1 downto 0);
    v_pre    : std_logic;
  end record;


  function slv_to_sr(slv : std_logic_vector(SR_DATA_WIDTH-1 downto 0)) return sr_t;
  function sr_to_slv(m : std_logic_vector(m_DATA_WIDTH-1 downto 0); t_pre : std_logic_vector(t_Pre_DATA_WIDTH-1 downto 0); v_pre : std_logic) return std_logic_vector;
  constant SR_T_NULL : sr_t := ((others=>'0'),(others=>'0'),'0');

  type interval_t is record
    max : std_logic_vector(TIMESTAMP_WIDTH - 1 downto 0);
    min : std_logic_vector(TIMESTAMP_WIDTH - 1 downto 0);
  end record;
  constant INTERVAL_T_NULL  : interval_t := (std_logic_vector(to_unsigned(0, TIMESTAMP_WIDTH)), std_logic_vector(to_unsigned(0, TIMESTAMP_WIDTH)));

  type ft_tuple_t is record
    value : std_logic; 
    time  : std_logic_vector(TIMESTAMP_WIDTH - 1 downto 0);
  end record;

  constant FT_TUPLE_T_NULL : ft_tuple_t := ('0', (others => '0'));
  constant FT_TUPLE_T_LEN  : integer    := 1 + TIMESTAMP_WIDTH;

  -- synchronous output logic
  subtype  ft_logic_t is std_logic_vector(2-1 downto 0);
  constant FT_TRUE  : ft_logic_t := "01";
  constant FT_FALSE : ft_logic_t := "00";
  constant FT_MAYBE : ft_logic_t := "10";

  function ts_to_slv(ts  : ft_tuple_t) return std_logic_vector;
  function slv_to_ts(slv : std_logic_vector) return ft_tuple_t;

  type operand_t is record
    value          : std_logic_vector(9-1 downto 0);
    is_memory_addr : std_logic;
    is_immediate   : std_logic;
  end record;

  constant OPERAND_T_NULL     : operand_t := ((others => '0'), '0', '0');

  type instruction_t is record
    command      : operator_t;
    op1          : operand_t;
    op2          : operand_t;
    intervalAddr : std_logic_vector(8-1 downto 0);
    memoryAddr   : std_logic_vector(7-1 downto 0);
  end record;

  function slv_to_instruction(slv : std_logic_vector(COMMAND_WIDTH-1 downto 0)) return instruction_t;
  constant INSTRUCTION_T_NULL     : instruction_t := (OP_FT_NOT, OPERAND_T_NULL, OPERAND_T_NULL, (others => '0'), (others => '0'));


  type ft_queue_in_t is record
    pc                : std_logic_vector(log2c(NUMBER_OF_QUEUES) - 1 downto 0);
    op1_num           : std_logic_vector(log2c(NUMBER_OF_QUEUES) - 1 downto 0);
    op2_num           : std_logic_vector(log2c(NUMBER_OF_QUEUES) - 1 downto 0);
    --is_load_command   : std_logic;
    command           : operator_t;
    need_op2          : std_logic;--only AND, UNTIL operator need op2
    new_result        : ft_tuple_t;
    new_result_rdy    : std_logic;
    have_new_result   : std_logic;
    opNum_rdy         : std_logic;
    is_op1_atomic     : std_logic;
    is_op2_atomic     : std_logic;
  end record;

  type debug_t is record
    have_new_result : std_logic;
    new_result_rdy : std_logic;
    new_result : ft_tuple_t;
    command : operator_t;
    interval : interval_t;
    pc_debug : std_logic_vector(log2c(ROM_LEN) - 1 downto 0);
    have_new_result_intermediate : std_logic;
    new_result_rdy_intermediate :  std_logic;
    finish : std_logic;
  end record;

  type queue_state_t is (RESET, IDLE, FETCH_RD, NEW_INPUT_CHECK, FETCH_PTR, WAIT_NEW_RESULT, UPDATE_PTR, WRITE_NEW_RESULT_AND_PTR);
  
  type ft_queue_async_out_t is record
    head  : ft_tuple_t;
    tail  : ft_tuple_t;
    empty : std_logic;
  end record;
  constant FT_QUEUE_ASYNC_OUT_T_NULL : ft_queue_async_out_t := (FT_TUPLE_T_NULL, FT_TUPLE_T_NULL, '0');

  type ft_queue_out_t is record
    op1           : ft_tuple_t;
    op2           : ft_tuple_t;
    state         : queue_state_t;
    isEmpty_1     : std_logic;
    isEmpty_2     : std_logic;
    doSelfLoop    : std_logic;
    ptr_write     : std_logic;
  end record;

  --constant FT_QUEUE_OUT_T_NULL : ft_queue_out_t := (FT_QUEUE_ASYNC_OUT_T_NULL, FT_FALSE);
  constant FT_QUEUE_OUT_T_NULL : ft_queue_out_t := (FT_TUPLE_T_NULL,FT_TUPLE_T_NULL, RESET, '1', '1','1','0');

  component ft_queue is
    port (
      clk                 : in  std_logic;
      res_n               : in  std_logic;
      i                   : in  ft_queue_in_t;
      o                   : out ft_queue_out_t;
      map_rdAddr          : in std_logic_vector(log2c(ROM_LEN)-1 downto 0);
      map_wrAddr          : in std_logic_vector(log2c(ROM_LEN)-1 downto 0);
      map_sync_data       : out std_logic_vector(ft_logic_t'LENGTH-1 downto 0);
      map_async_data      : out std_logic_vector(FT_TUPLE_T_LEN-1+1 downto 0)
      );
  end component;

  component ft_monitor_fsm is
    port (clk                     : in  std_logic;  -- clock signal
          res_n                   : in  std_logic;  -- reset signal (active low)
          violated                : out std_logic;  -- violated signal (result is not correct)
          violatedValid           : out std_logic;
          trigger                 : in  std_logic;
          atomics                 : in  std_logic_vector(ATOMICS_WIDTH-1 downto 0);  -- invariant-checker-violated-bits from fifo
          timestamp               : in  std_logic_vector(TIMESTAMP_WIDTH-1 downto 0);  -- invariant-checker-violated-bits from fifo
          imemAddr                : out std_logic_vector(log2c(ROM_LEN) -1 downto 0);
          imemData                : in  std_logic_vector(COMMAND_WIDTH-1 downto 0);
          interval_memory_data    : in  std_logic_vector(2*TIMESTAMP_WIDTH-1 downto 0);
          interval_memory_addr    : out std_logic_vector(log2c(INTERVAL_MEMORY_LEN) -1 downto 0);
          pt_data_memory_addr     : out std_logic_vector(log2c(DATA_MEMORY_LEN) -1 downto 0);
          pt_data_memory_data     : in  std_logic;
          sync_out                : out ft_logic_t;
          async_out               : out ft_tuple_t;
          finish                  : out std_logic;
          data_memory_async_data  : out std_logic_vector(FT_TUPLE_T_LEN-1+1 downto 0);
          data_memory_async_empty : out std_logic;
          data_memory_sync_data   : out ft_logic_t;
          data_memory_addr        : in  std_logic_vector(log2c(ROM_LEN) - 1 downto 0);
          
          this_new_result         : out  std_logic;
          this_sync_out_data_time : out std_logic_vector(TIMESTAMP_WIDTH - 1 downto 0);
          --this_sync_out_data_value : out std_logic

              --Pei: signal for writing output
          debug : out debug_t
          --have_new_result : out std_logic;
          --new_result_rdy : out std_logic;
          --new_result : out ft_tuple_t;
          --command : out operator_t;
          --pc_debug : out std_logic_vector(log2c(ROM_LEN) - 1 downto 0);
          --have_new_result_intermediate : out std_logic;
          --new_result_rdy_intermediate : out std_logic
          
          );
  end component;

  component ft_monitor is
    port (clk                     : in  std_logic;  -- clock signal
          reset_n                 : in  std_logic;  -- reset signal (low active)
          en                      : in  std_logic;  -- en signal
          trigger                 : in  std_logic;
          atomics                 : in  std_logic_vector(ATOMICS_WIDTH-1 downto 0);  -- invariant checker result
          timestamp               : in  std_logic_vector(TIMESTAMP_WIDTH-1 downto 0);
          program_addr            : in  std_logic_vector(MEMBUS_ADDR_WIDTH-1 downto 0);  -- rom address for programming
          program_data            : in  std_logic_vector(MEMBUS_DATA_WIDTH-1 downto 0);  -- programming data for rom
          program_imem            : in  std_logic;
          program_interval_memory : in  std_logic;
          violated                : out std_logic;  -- violated signal
          violated_valid          : out std_logic;
          pt_data_memory_addr     : out std_logic_vector(log2c(DATA_MEMORY_LEN) - 1 downto 0);
          pt_data_memory_data     : in  std_logic;
          sync_out                : out ft_logic_t;
          finish                  : out std_logic;
          data_memory_async_data  : out std_logic_vector(FT_TUPLE_T_LEN-1+1 downto 0);
          data_memory_async_empty : out std_logic;
          data_memory_sync_data   : out ft_logic_t;
          data_memory_addr        : in  std_logic_vector(log2c(ROM_LEN) - 1 downto 0);
          
          --Pei: signal for simulation to replace spy function
          
          this_new_result         : out  std_logic;
          this_sync_out_data_time  : out std_logic_vector(TIMESTAMP_WIDTH - 1 downto 0);
          --this_sync_out_data_value : out std_logic
          debug : out debug_t
          --have_new_result : out std_logic;
          --new_result_rdy : out std_logic;
          --new_result : out ft_tuple_t;
          --command : out operator_t;
          --pc_debug : out std_logic_vector(log2c(ROM_LEN) - 1 downto 0);
          --have_new_result_intermediate : out std_logic;
          --new_result_rdy_intermediate : out std_logic
          );
  end component;
  
end package;

package body ft_monitor_pkg is
  function ts_to_slv(ts : ft_tuple_t) return std_logic_vector is
    variable ret : std_logic_vector(TIMESTAMP_WIDTH downto 0);
  begin
    ret := ts.value & ts.time;
    return ret;
  end function;

  function slv_to_ts(slv : std_logic_vector) return ft_tuple_t is
    variable ret : ft_tuple_t;
  begin
    ret.value := slv(TIMESTAMP_WIDTH);
    ret.time  := slv(TIMESTAMP_WIDTH-1 downto 0);
    return ret;
  end function;

  function slv_to_operand(slv : std_logic_vector(10-1 downto 0)) return operand_t is
    variable ret : operand_t;
  begin
    ret.is_immediate   := slv(8);
    ret.is_memory_addr := slv(9);
    ret.value          := slv(9-1 downto 0);

    return ret;
  end function;

  function slv_to_instruction(slv : std_logic_vector(COMMAND_WIDTH-1 downto 0)) return instruction_t is
    variable ret : instruction_t;
  begin
    ret.command      := slv(40-1 downto 35);
    ret.op1          := slv_to_operand(slv(35-1 downto 25));
    ret.op2          := slv_to_operand(slv(25-1 downto 15));
    ret.intervalAddr := slv(15-1 downto 7);
    ret.memoryAddr   := slv(7-1 downto 0);

    return ret;
  end function;

  function slv_to_sr(slv : std_logic_vector(SR_DATA_WIDTH-1 downto 0)) return sr_t is
    variable ret : sr_t;
  begin
    ret.m        := slv(t_pre_DATA_WIDTH+m_DATA_WIDTH downto t_pre_DATA_WIDTH+1);
    ret.t_pre    := slv(t_pre_DATA_WIDTH downto 1);
    ret.v_pre    := slv(0);
    return ret;
  end function;

  function sr_to_slv(m : std_logic_vector(m_DATA_WIDTH-1 downto 0); t_pre : std_logic_vector(t_pre_DATA_WIDTH-1 downto 0); v_pre : std_logic) return std_logic_vector is
    variable ret : std_logic_vector(SR_DATA_WIDTH-1 downto 0);
  begin
    ret(t_pre_DATA_WIDTH+m_DATA_WIDTH downto t_pre_DATA_WIDTH+1)  := m;
    ret(t_pre_DATA_WIDTH downto 1)                                := t_pre;
    ret(0)                                                        := v_pre;
    return ret;
  end function;

end package body;
