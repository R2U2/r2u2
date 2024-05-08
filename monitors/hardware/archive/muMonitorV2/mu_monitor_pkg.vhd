-------------------------------------------------------------------------------
-- Project    : CevTes RVU (Runtime Verification Unit)
-------------------------------------------------------------------------------
-- File       : mu_monitor_pkg.vhd
-- Author     : Daniel Schachinger, Patrick Moosbrugger, Andreas Hagmann
-- Copyright  : 2011, Thomas Reinbacher (treinbacher@ecs.tuwien.ac.at)
--              Vienna University of Technology, ECS Group
-------------------------------------------------------------------------------
-- Description:  Package for mu_monitor-constants and components.
-------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pkg.all;
use work.cevLib_unsigned_pkg.all;
use work.log_input_pkg.all;

package mu_monitor_pkg is
  subtype  operator_t is std_logic_vector(5-1 downto 0);
  --------------------------------------------------------------------
  --                          CONSTANTS                             --
  --------------------------------------------------------------------
  constant TIMESTAMP_WIDTH     : integer := 16;

  -- constant TIMESTAMP_WIDTH     : integer := 48;
--  constant ATOMICS_WIDTH       : integer := 10;
  constant ROM_LEN             : integer := 64;  -- number of rom entries
  constant DATA_MEMORY_LEN     : integer := ROM_LEN;
  constant BOX_MEMORY_LEN      : integer := 32;
  constant DOT_BUFFER_LEN      : integer := 32;  -- number of buffers
  constant DOT_BUFFER_SIZE     : integer := 64;  -- size of one buffer
  constant INTERVAL_MEMORY_LEN : integer := BOX_MEMORY_LEN + DOT_BUFFER_LEN;
  constant COMMAND_WIDTH       : integer := 40;  -- width of mu_monitor-instruction
  -- This is for the Prom and intervall memorys which share the same bus
  constant MEMBUS_DATA_WIDTH   : integer := max(2*TIMESTAMP_WIDTH, COMMAND_WIDTH);
  constant MEMBUS_ADDR_WIDTH   : integer := max(log2c(ROM_LEN), log2c(INTERVAL_MEMORY_LEN));
  --Pei: constant for status register
  --constant mPre_DATA_WIDTH : integer := 10;
  constant m_DATA_WIDTH : integer := TIMESTAMP_WIDTH;
  constant t_pre_DATA_WIDTH : integer := TIMESTAMP_WIDTH;
  --constant mUp_DATA_WIDTH : integer := TIMESTAMP_WIDTH;
  --constant mDown_DATA_WIDTH : integer := TIMESTAMP_WIDTH;
  --constant SR_DATA_WIDTH : integer := mPre_DATA_WIDTH + mUp_DATA_WIDTH + mDown_DATA_WIDTH + 2;
  --constant SR_DATA_WIDTH : integer := mPre_DATA_WIDTH + mUp_DATA_WIDTH + mDown_DATA_WIDTH + 2;
  constant SR_DATA_WIDTH : integer := m_DATA_WIDTH + t_pre_DATA_WIDTH + 1;

  subtype program_counter_t is std_logic_vector(log2c(ROM_LEN) - 1 downto 0);
  constant PROGRAMM_COUNTER_DEFAULT : program_counter_t := (others=>'0');

  -- Operators
  constant OP_FALSE              : operator_t := "00000";
  constant OP_TRUE               : operator_t := "00001";
  constant OP_ATOMIC             : operator_t := "00010";
  --Pei: revise the OP_LOAD op code to correspond with software
  constant OP_LOAD               : operator_t := "11100";
  --constant OP_LOAD               : operator_t := "00010";
  constant OP_NOT                : operator_t := "00011";
  constant OP_AND                : operator_t := "00100";
  constant OP_OR                 : operator_t := "00101";
  constant OP_IMPLICIT           : operator_t := "00110";
  constant OP_EQUIVALENT         : operator_t := "00111";
  constant OP_PREVIOUSLY         : operator_t := "01000";
  constant OP_EVENTUALLY         : operator_t := "01001";
  constant OP_ALWAYS             : operator_t := "01010";
  constant OP_START              : operator_t := "01011";
  constant OP_END                : operator_t := "01100";
  constant OP_INTERVAL           : operator_t := "01101";
  constant OP_SINCE              : operator_t := "01110";
  constant OP_MTL_DIAMONDDIAMOND : operator_t := "01111";
  constant OP_MTL_DIAMONDDOT     : operator_t := "10000";
  constant OP_MTL_BOXBOX         : operator_t := "10001";
  constant OP_MTL_BOXDOT         : operator_t := "10010";
  constant OP_MTL_SINCE          : operator_t := "10011";
  constant OP_FT_NOT             : operator_t := "10100";
  constant OP_FT_AND             : operator_t := "10101";
  constant OP_FT_BOXBOX          : operator_t := "10110";
  constant OP_FT_BOXDOT          : operator_t := "10111";
  constant OP_FT_DIAMONDDIAMOND  : operator_t := "11000";
  constant OP_FT_DIAMONDDOT      : operator_t := "11001";
  constant OP_FT_UNTIL           : operator_t := "11010";
  constant OP_FT_IMPLICIT        : operator_t := "11011";
  constant OP_NOP                : operator_t := "11110";
  constant OP_END_SEQUENCE       : operator_t := "11111";

  component mu_monitor is
    port (
      clk                     : in  std_logic;  -- clock signal
      reset_n                 : in  std_logic;  -- reset signal (low active)
      en                      : in  std_logic;  -- en signal
      atomics                 : in  std_logic_vector(ATOMICS_WIDTH - 1 downto 0);  -- invariant checker result
      timestamp               : in  std_logic_vector(TIMESTAMP_WIDTH - 1 downto 0);
      program_addr            : in  std_logic_vector(MEMBUS_ADDR_WIDTH - 1 downto 0);  -- rom address for programming
      program_data            : in  std_logic_vector(2*TIMESTAMP_WIDTH -1 downto 0);  -- programming data for rom
      program_imem            : in  std_logic;
      program_interval_memory : in  std_logic;
      valid                   : out std_logic;
      violated                : out std_logic;  -- violated signal
      violated_valid          : out std_logic;
      finish                  : out std_logic;
      data_memory_addr        : in  std_logic_vector(log2c(ROM_LEN)-1 downto 0);
      data_memory_data        : out std_logic
      );
  end component mu_monitor;

  type sr_t is record
    m        : std_logic_vector(m_DATA_WIDTH-1 downto 0);
    t_pre    : std_logic_vector(t_pre_DATA_WIDTH-1 downto 0);
    v_pre    : std_logic;
  end record;

  type operands_t is record
    op1Pre : std_logic;
    op2Pre : std_logic;
    op1Now : std_logic;
    op2Now : std_logic;
    fwd1   : std_logic;
    fwd2   : std_logic;
    now    : std_logic;
    pre    : std_logic;
  end record;
  constant OPERANDS_T_NULL : operands_t := ('0', '0', '0', '0', '0', '0', '0', '0');




  type data_memory_in_t is record
    rdAddrA : std_logic_vector(log2c(ROM_LEN) - 1 downto 0);
    rdAddrB : std_logic_vector(log2c(ROM_LEN) - 1 downto 0);
    rdAddrC : std_logic_vector(log2c(ROM_LEN) - 1 downto 0);
    wrAddr  : std_logic_vector(log2c(ROM_LEN) - 1 downto 0);
    wrData  : std_logic;                -- write data
    write   : std_logic;
  end record;

  type data_memory_out_t is record
    rdDataA : std_logic;
    rdDataB : std_logic;
    rdDataC : std_logic;
  end record;

  type interval_t is record
    max : std_logic_vector(TIMESTAMP_WIDTH - 1 downto 0);
    min : std_logic_vector(TIMESTAMP_WIDTH - 1 downto 0);
  end record;
  constant INTERVAL_T_WIDTH : integer    := 2*TIMESTAMP_WIDTH;
  constant INTERVAL_T_NULL  : interval_t := (std_logic_vector(to_unsigned(0, TIMESTAMP_WIDTH)), std_logic_vector(to_unsigned(0, TIMESTAMP_WIDTH)));

  type ft_tuple_t is record
    value : std_logic; 
    time  : std_logic_vector(TIMESTAMP_WIDTH - 1 downto 0);
  end record;


  constant TIMESTAMP_T_WIDTH : integer     := TIMESTAMP_WIDTH + 1;
  constant TIMESTAMP_T_NULL  : ft_tuple_t := ('0', (others => '0'));

  function ts_to_slv(ts  : ft_tuple_t) return std_logic_vector;
  function slv_to_ts(slv : std_logic_vector) return ft_tuple_t;

  type timestampTuple_t is record
    start : ft_tuple_t;
    stop  : ft_tuple_t;
  end record;
  constant TIMESTAMPTUPLE_T_WIDTH : integer          := TIMESTAMP_T_WIDTH * 2;
  constant TIMESTAMPTUPLE_T_NULL  : timestampTuple_t := (TIMESTAMP_T_NULL, TIMESTAMP_T_NULL);

  function tst_to_slv(tst : timestampTuple_t) return std_logic_vector;
  function slv_to_tst(slv : std_logic_vector) return timestampTuple_t;

  type box_memory_in_t is record
    rdAddr : std_logic_vector(log2c(BOX_MEMORY_LEN)-1 downto 0);  -- read address
    wrData : std_logic_vector(TIMESTAMP_T_WIDTH - 1 downto 0);    -- write data
    write  : std_logic;
  end record;

  type box_memory_out_t is record
    rdData : std_logic_vector(TIMESTAMP_T_WIDTH - 1 downto 0);  -- write data
  end record;

  type list_array_in_t is record
    timestamp       : std_logic_vector(TIMESTAMP_WIDTH - 1 downto 0);  -- timestamp to data
    --fetch_pointer   : std_logic;
    sel             : std_logic;        -- select buffer
    add_start       : std_logic;        -- store start timestamp
    add_end         : std_logic;  -- add end timestamp to start and add both to the list
    set_tail        : std_logic;  -- clear the list and add one element (start and end)
    reset_tail      : std_logic;  -- clear the list and set tail element (start only)
    drop_tail       : std_logic;        -- clear the tail element
    delete          : std_logic;        -- delete the head element
    fetch_buffer_nr : std_logic_vector(log2c(DOT_BUFFER_LEN) - 1 downto 0);
    buffer_nr       : std_logic_vector(log2c(DOT_BUFFER_LEN) - 1 downto 0);
  end record;

  type list_array_out_t is record
    tail  : timestampTuple_t;
    head  : timestampTuple_t;
    empty : std_logic;
  end record;

  type operand_t is record
    value          : std_logic_vector(9-1 downto 0);
    is_memory_addr : std_logic;
    is_immediate   : std_logic;
  end record;
  function slv_to_operand(slv : std_logic_vector(10-1 downto 0)) return operand_t;
  constant OPERAND_T_NULL     : operand_t := ((others => '0'), '0', '0');

  constant SR_T_NULL : sr_t := ((others=>'0'),(others=>'0'),'0');

  type instruction_t is record
    command      : operator_t;
    op1          : operand_t;
    op2          : operand_t;
    intervalAddr : std_logic_vector(8-1 downto 0);
    memoryAddr   : std_logic_vector(7-1 downto 0);
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

  function slv_to_instruction(slv : std_logic_vector(COMMAND_WIDTH-1 downto 0)) return instruction_t;
  constant INSTRUCTION_T_NULL     : instruction_t := (OP_NOT, OPERAND_T_NULL, OPERAND_T_NULL, (others => '0'), (others => '0'));

  --pei: new function
  function slv_to_sr(slv : std_logic_vector(SR_DATA_WIDTH-1 downto 0)) return sr_t;
  --function sr_to_slv(last_value : std_logic; mUp : std_logic_vector(mUp_DATA_WIDTH-1 downto 0); mPre : std_logic_vector(mPre_DATA_WIDTH-1 downto 0)) return std_logic_vector;
  --function sr_to_slv(last_value : std_logic; mUp : std_logic_vector(mUp_DATA_WIDTH-1 downto 0); mDown : std_logic_vector(mDown_DATA_WIDTH-1 downto 0);
  --                   mPre : std_logic_vector(mPre_DATA_WIDTH-1 downto 0); p : std_logic) return std_logic_vector;
  function sr_to_slv(m : std_logic_vector(m_DATA_WIDTH-1 downto 0); t_pre : std_logic_vector(t_Pre_DATA_WIDTH-1 downto 0); v_pre : std_logic) return std_logic_vector;
  

  component list_array is
    generic (
      BUFFER_SIZE    : integer;         -- must be power of 2
      DOT_BUFFER_LEN : integer
      );
    port (
      clk   : in  std_logic;            -- clock signal
      res_n : in  std_logic;
      i     : in  list_array_in_t;
      o     : out list_array_out_t
      );
  end component;

  -- pipeline stuff
  type fetch_register_t is record
    command         : instruction_t;
    program_counter : program_counter_t;
  end record;
  constant FETCH_REGISTER_T_NULL : fetch_register_t := (INSTRUCTION_T_NULL, PROGRAMM_COUNTER_DEFAULT);--(others => '0'));

  type fetch_in_t is record
    start   : std_logic;
    nxt_ack : std_logic;
    memData : std_logic_vector(COMMAND_WIDTH - 1 downto 0);
  end record;

  type fetch_out_t is record
    fin     : std_logic;
    reg     : fetch_register_t;
    memAddr : std_logic_vector(log2c(ROM_LEN) - 1 downto 0);
  end record;

  type load_register_t is record
    command          : operator_t;
    memoryAddr       : std_logic_vector(7-1 downto 0);
    program_counter  : program_counter_t;  
    operand          : operands_t;
    interval         : interval_t;
    timestamp_buffer : ft_tuple_t;
  end record;
  constant LOAD_REGISTER_T_NULL : load_register_t := (OP_NOP, (others => '0'), PROGRAMM_COUNTER_DEFAULT, OPERANDS_T_NULL, INTERVAL_T_NULL, TIMESTAMP_T_NULL);

  type load_in_t is record
    prev_fin             : std_logic;
    nxt_ack              : std_logic;
    calcFin              : std_logic;
    reg                  : fetch_register_t;
    atomics              : std_logic_vector(ATOMICS_WIDTH - 1 downto 0);
    last_atomics         : std_logic_vector(ATOMICS_WIDTH - 1 downto 0);
    interval_memory_data : std_logic_vector(2*TIMESTAMP_WIDTH - 1 downto 0);
    calc_result          : std_logic;
    calc_idle            : std_logic;
    initialized          : std_logic;
    preMemory            : data_memory_out_t;
    nowMemory            : data_memory_out_t;
  end record;

  type load_out_t is record
    preMemory            : data_memory_in_t;
    nowMemory            : data_memory_in_t;
    interval_memory_addr : std_logic_vector(log2c(INTERVAL_MEMORY_LEN)-1 downto 0);
    reg                  : load_register_t;
    fin                  : std_logic;
    ack                  : std_logic;
    --fetch_list_pointer   : std_logic;
    buffer_nr            : std_logic_vector(log2c(DOT_BUFFER_LEN) - 1 downto 0);
  end record;

  type calc_register_t is record
    program_counter : program_counter_t;
    result          : std_logic;
  end record;
  constant CALC_REGISTER_T_NULL : calc_register_t := (PROGRAMM_COUNTER_DEFAULT, '0');

  type calc_in_t is record
    prev_fin  : std_logic;
    nxt_ack   : std_logic;
    reg       : load_register_t;
    time      : std_logic_vector(TIMESTAMP_WIDTH - 1 downto 0);
    dotMemory : list_array_out_t;
    boxMemory : box_memory_out_t;
  end record;

  type calc_out_t is record
    violated_valid : std_logic;
    violated       : std_logic;
    fin            : std_logic;
    ack            : std_logic;
    idle           : std_logic;
    initialized    : std_logic;
    resultNow      : std_logic;
    reg            : calc_register_t;
    dotMemory      : list_array_in_t;
    boxMemory      : box_memory_in_t;
    calc_finish    : std_logic;
  end record;

  type write_back_in_t is record
    prev_fin : std_logic;
    reg      : calc_register_t;
  end record;

  type write_back_out_t is record
    ack       : std_logic;
    nowMemory : data_memory_in_t;
  end record;

  component fetch_stage is
    port (
      clk     : in  std_logic;
      reset_n : in  std_logic;
      i       : in  fetch_in_t;
      o       : out fetch_out_t
      );
  end component;

  component load_stage
    port (
      clk     : in  std_logic;
      reset_n : in  std_logic;
      i       : in  load_in_t;
      o       : out load_out_t
      );
  end component;

  component calc_stage is
    port (
      clk     : in  std_logic;
      reset_n : in  std_logic;
      i       : in  calc_in_t;
      o       : out calc_out_t
      );
  end component;

  component write_back_stage is
    port (
      clk     : in  std_logic;
      reset_n : in  std_logic;
      i       : in  write_back_in_t;
      o       : out write_back_out_t
      );
  end component;

end mu_monitor_pkg;

package body mu_monitor_pkg is
  function tst_to_slv(tst : timestampTuple_t) return std_logic_vector is
    variable ret : std_logic_vector(TIMESTAMPTUPLE_T_WIDTH - 1 downto 0);
  begin
    ret := tst.start.value & tst.start.time & tst.stop.value & tst.stop.time;
    return ret;
  end function;

  function slv_to_tst(slv : std_logic_vector) return timestampTuple_t is
    variable ret   : timestampTuple_t;
    variable slv_t : std_logic_vector(TIMESTAMP_T_WIDTH - 1 downto 0);
  begin
    slv_t     := slv(TIMESTAMPTUPLE_T_WIDTH - 1 downto TIMESTAMPTUPLE_T_WIDTH - TIMESTAMP_WIDTH - 1);
    ret.start := slv_to_ts(slv_t);
    ret.stop  := slv_to_ts(slv(TIMESTAMP_T_WIDTH - 1 downto 0));
    return ret;
  end function;

  function ts_to_slv(ts : ft_tuple_t) return std_logic_vector is
    variable ret : std_logic_vector(TIMESTAMP_T_WIDTH - 1 downto 0);
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

  --Pei: new function
  function slv_to_sr(slv : std_logic_vector(SR_DATA_WIDTH-1 downto 0)) return sr_t is
    variable ret : sr_t;
  begin
    ret.m        := slv(t_pre_DATA_WIDTH+m_DATA_WIDTH downto t_pre_DATA_WIDTH+1);
    ret.t_pre    := slv(t_pre_DATA_WIDTH downto 1);
    ret.v_pre    := slv(0);
    return ret;
  end function;
  
  --function sr_to_slv(last_value: std_logic; mUp : std_logic_vector(mUp_DATA_WIDTH-1 downto 0); mPre : std_logic_vector(mPre_DATA_WIDTH-1 downto 0)) return std_logic_vector is
  --  variable ret : std_logic_vector(SR_DATA_WIDTH-1 downto 0);
  --begin
  --  ret(SR_DATA_WIDTH-1)                                                                            := last_value;
  --  ret(mUp_DATA_WIDTH+mDown_DATA_WIDTH+mPre_DATA_WIDTH downto mDown_DATA_WIDTH+mPre_DATA_WIDTH+1)  := mUp;
  --  ret(mDown_DATA_WIDTH+mPre_DATA_WIDTH downto mPre_DATA_WIDTH+1)                                  := (others=>'0');
  --  ret(mPre_DATA_WIDTH downto 1)                                                                   := mPre;
  --  ret(0)                                                                                          := '0';
  --  return ret;
  --end function;

  function sr_to_slv(m : std_logic_vector(m_DATA_WIDTH-1 downto 0); t_pre : std_logic_vector(t_pre_DATA_WIDTH-1 downto 0); v_pre : std_logic) return std_logic_vector is
    variable ret : std_logic_vector(SR_DATA_WIDTH-1 downto 0);
  begin
    ret(t_pre_DATA_WIDTH+m_DATA_WIDTH downto t_pre_DATA_WIDTH+1)  := m;
    ret(t_pre_DATA_WIDTH downto 1)                                := t_pre;
    ret(0)                                                        := v_pre;
    return ret;
  end function;



end package body;
