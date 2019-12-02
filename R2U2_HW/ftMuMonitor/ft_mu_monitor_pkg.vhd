-------------------------------------------------------------------------------
-- Project    : CevTes RVU (Runtime Verification Unit)
-------------------------------------------------------------------------------
-- File       : mu_monitor_pkg.vhd
-- Author     : Andreas Hagmann (ahagmann@ecs.tuwien.ac.at)
-- Copyright  : 2012, Thomas Reinbacher (treinbacher@ecs.tuwien.ac.at)
--              Vienna University of Technology, ECS Group
-------------------------------------------------------------------------------
-- Description:  Package for mu_monitor-constants and components.                    
------------------------------------------------------------------------------- 

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pkg.all;
use work.cevLib_unsigned_pkg.all;
use work.mu_monitor_pkg.all;
use work.log_input_pkg.all;

package ft_mu_monitor_pkg is
  constant NUMBER_OF_QUEUES         : integer := ROM_LEN;--maximum instruction
  constant NUMBER_OF_QUEUE_ELEMENTS : integer := 2048;
  constant QUEUE_SIZE : integer := 32;
  constant DATA_QUEUE_SIZE : integer := NUMBER_OF_QUEUES*QUEUE_SIZE;

  constant FT_TUPLE_T_NULL : ft_tuple_t := ('0', (others => '0'));
  constant FT_TUPLE_T_LEN  : integer    := 1 + TIMESTAMP_WIDTH;

  -- synchronous output logic
  subtype  ft_logic_t is std_logic_vector(2-1 downto 0);
  constant FT_TRUE  : ft_logic_t := "01";
  constant FT_FALSE : ft_logic_t := "00";
  constant FT_MAYBE : ft_logic_t := "10";

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

  component ft_mu_monitor_fsm is
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

  component ft_mu_monitor is
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

package body ft_mu_monitor_pkg is


end package body;
