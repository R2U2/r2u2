------------------------------------------------------------------------------
-- Project    : CevTes RVU (Runtime Verification Unit)
-------------------------------------------------------------------------------
-- File       : mu_monitor.vhd
-- Author     : Andreas Hagmann (ahagmann@ecs.tuwien.ac.at)
-- Copyright  : 2012, Thomas Reinbacher (treinbacher@ecs.tuwien.ac.at)
--              Vienna University of Technology, ECS Group
-------------------------------------------------------------------------------
-- Description: muMonitor main
-- PAMO NOTE: prinzipiell koennten auch past time befehle ausgefuert werden
--            deren ergebnisse dann sinnlos w?ren, daher muss eigentlich sichergestellt sein,
--            dass in dem compilierten bin?r programm keine pt operatoren drinnen sind! (operatoren siehe mu_monitor_pkg.vhd)
-------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
library work;
use work.cevLib_unsigned_pkg.all;
use work.math_pkg.all;
use work.mu_monitor_pkg.all;
use work.ft_mu_monitor_pkg.all;
use work.log_input_pkg.all;
use work.ram_pkg.all;

entity ft_mu_monitor is
  port (
    clk                     : in  std_logic;  -- clock signal
    reset_n                 : in  std_logic;  -- reset signal (low active)
    en                      : in  std_logic;  -- en signal
    trigger                 : in  std_logic;
    atomics                 : in  std_logic_vector(ATOMICS_WIDTH - 1 downto 0);  -- invariant checker result
    timestamp               : in  std_logic_vector(TIMESTAMP_WIDTH - 1 downto 0);
    program_addr            : in  std_logic_vector(MEMBUS_ADDR_WIDTH - 1 downto 0);  -- rom address for programming
    program_data            : in  std_logic_vector(MEMBUS_DATA_WIDTH -1 downto 0);  -- programming data for rom
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
    this_new_result         : out std_logic;
    this_sync_out_data_time : out std_logic_vector(TIMESTAMP_WIDTH-1 downto 0);
    --this_sync_out_data_value: out std_logic
    
    --Pei: signal for writing output
    debug : out debug_t

    );
end entity;

architecture arch of ft_mu_monitor is
  type registerType is record
    atomics      : std_logic_vector(ATOMICS_WIDTH-1 downto 0);
    last_atomics : std_logic_vector(ATOMICS_WIDTH-1 downto 0);
    time         : std_logic_vector(TIMESTAMP_WIDTH-1 downto 0);
  end record;

  -- variables / constants

  constant registerReset : registerType := (
    (others => '0'),
    (others => '0'),
    (others => '1')
    );

--  signal this, this_nxt     : registerType;
  signal mu_monitor_reset_n : std_logic;

  signal imemRdAddr : std_logic_vector(log2c(ROM_LEN) - 1 downto 0);
  signal imemWrAddr : std_logic_vector(log2c(ROM_LEN) - 1 downto 0);
  signal imemWrData : std_logic_vector(COMMAND_WIDTH - 1 downto 0);
  signal imemRdData : std_logic_vector(COMMAND_WIDTH - 1 downto 0);
  signal imemWrite  : std_logic;

  signal intMemRdAddr : std_logic_vector(log2c(INTERVAL_MEMORY_LEN) - 1 downto 0);
  signal intMemWrAddr : std_logic_vector(log2c(INTERVAL_MEMORY_LEN) - 1 downto 0);
  signal intMemWrData : std_logic_vector(2*TIMESTAMP_WIDTH - 1 downto 0);
  signal intMemRdData : std_logic_vector(2*TIMESTAMP_WIDTH - 1 downto 0);
  signal intMemWrite  : std_logic;

  type instruction_memory_out_t is record
    rdData : std_logic_vector(COMMAND_WIDTH - 1 downto 0);
  end record;

begin
  -- instantiate components
  -- imem
  imem_c : dp_ram
    generic map(
      ADDR_WIDTH => log2c(ROM_LEN),
      DATA_WIDTH => COMMAND_WIDTH
      )
    port map (
      clk    => clk,
      rdAddr => imemRdAddr,
      wrAddr => imemWrAddr,
      wrData => imemWrData,
      write  => imemWrite,
      rdData => imemRdData
      );

  -- interval memory
  intMem_c : dp_ram
    generic map(
      ADDR_WIDTH => log2c(INTERVAL_MEMORY_LEN),
      DATA_WIDTH => 2*TIMESTAMP_WIDTH
      )
    port map (
      clk    => clk,
      rdAddr => intMemRdAddr,
      wrAddr => intMemWrAddr,
      wrData => intMemWrData,
      write  => intMemWrite,
      rdData => intMemRdData
      );

  ift_mu_monitor_fsm : ft_mu_monitor_fsm
    port map (
      clk                     => clk,
      res_n                   => mu_monitor_reset_n,
      violated                => violated,
      violatedValid           => violated_valid,
      trigger                 => trigger,
      atomics                 => atomics,
      timestamp               => timestamp,
      imemAddr                => imemRdAddr,
      imemData                => imemRdData,
      interval_memory_data    => intMemRdData,
      interval_memory_addr    => intMemRdAddr,
      pt_data_memory_addr     => pt_data_memory_addr,
      pt_data_memory_data     => pt_data_memory_data,
      sync_out                => sync_out,
      async_out               => open,
      finish                  => finish,
      data_memory_async_data  => data_memory_async_data,
      data_memory_async_empty => data_memory_async_empty,
      data_memory_sync_data   => data_memory_sync_data,
      data_memory_addr        => data_memory_addr,
      
      this_new_result       => this_new_result,
      this_sync_out_data_time  => this_sync_out_data_time,
      --this_sync_out_data_value  => this_sync_out_data_value

      debug => debug
      --have_new_result => have_new_result,
      --new_result_rdy => new_result_rdy,
      --new_result => new_result,
      --commandata_memory_sync_datad => command,
      --pc_debug => pc_debug,
      --have_new_result_intermediate => have_new_result_intermediate,
      --new_result_rdy_intermediate => new_result_rdy_intermediate


      );
      

  -- logic
  cominatorial : process(atomics, timestamp, imemRdData, intMemRdData, reset_n, en, program_imem, program_interval_memory, program_addr, program_data)
    --variable nxt : registerType;
  begin
    -- nxt := this;

    mu_monitor_reset_n <= reset_n and en;  -- low active reset signal

    -- program memories
    imemWrAddr <= program_addr(log2c(ROM_LEN) - 1 downto 0);
    imemWrData <= program_data(COMMAND_WIDTH-1 downto 0);
    imemWrite  <= program_imem;

    intMemWrAddr <= program_addr(log2c(INTERVAL_MEMORY_LEN) - 1 downto 0);
    intMemWrData <= program_data(2*TIMESTAMP_WIDTH-1 downto 0);
    intMemWrite  <= program_interval_memory;

    -- if en = '1' then
    --    if this.time /= timestamp then    -- new cycle
    --      fetch_i.start     <= '1';
    --      nxt.time          := timestamp;
    --      nxt.last_atomics  := this.atomics;
    --      nxt.atomics       := atomics;
    --     end if;
    --   end if;

    --   this_nxt <= nxt;
  end process;

  -- reg : process (clk , reset_n)
  -- begin
  --   if reset_n = '0' then
  --     this <= registerReset;
  --   elsif rising_edge (clk) then
  --     this <= this_nxt;
  --   end if;
  -- end process;

end architecture;
