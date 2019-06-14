------------------------------------------------------------------------------
-- Project    : CevTes RVU (Runtime Verification Unit)
-------------------------------------------------------------------------------
-- File       : mu_monitor.vhd
-- Author     : Andreas Hagmann (ahagmann@ecs.tuwien.ac.at)
-- Copyright  : 2012, Thomas Reinbacher (treinbacher@ecs.tuwien.ac.at)
--              Vienna University of Technology, ECS Group
-------------------------------------------------------------------------------
-- Description: muMonitor main
-------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.cevLib_unsigned_pkg.all;
use work.math_pkg.all;
use work.mu_monitor_pkg.all;
use work.log_input_pkg.all;
use work.ram_pkg.all;

entity mu_monitor is
  port (
    clk                     : in  std_logic;  -- clock signal
    reset_n                 : in  std_logic;  -- reset signal (low active)
    en                      : in  std_logic;  -- en signal
    atomics                 : in  std_logic_vector(ATOMICS_WIDTH - 1 downto 0);  -- invariant checker result
    timestamp               : in  std_logic_vector(TIMESTAMP_WIDTH - 1 downto 0);
    program_addr            : in  std_logic_vector(MEMBUS_ADDR_WIDTH - 1 downto 0);  -- rom address for programming
    program_data            : in  std_logic_vector(MEMBUS_DATA_WIDTH -1 downto 0);  -- programming data for rom
    program_imem            : in  std_logic;
    program_interval_memory : in  std_logic;
    valid                   : out std_logic;
    violated                : out std_logic;  -- violated signal
    violated_valid          : out std_logic;
    finish					: out std_logic;
    data_memory_addr        : in std_logic_vector(log2c(ROM_LEN)-1 downto 0);
    data_memory_data        : out std_logic
  );
end entity mu_monitor;

architecture arch of mu_monitor is
  type data_memory_array_in_t is array(1 downto 0) of data_memory_in_t;
  type data_memory_array_out_t is array(1 downto 0) of data_memory_out_t;

  type registerType is record
    memory_select : std_logic;
    atomics       : std_logic_vector(ATOMICS_WIDTH-1 downto 0);
    last_atomics  : std_logic_vector(ATOMICS_WIDTH-1 downto 0);
    time          : std_logic_vector(TIMESTAMP_WIDTH-1 downto 0);
    forward_data_mem : std_logic;
  end record;

  -- variables / constants

  constant registerReset : registerType := (
    '0',
    (others => '0'),
    (others => '0'),
    (others => '1'),
    '0'
    );

  signal this, this_nxt     : registerType;
  signal mu_monitor_reset_n : std_logic;

  signal dataMemory_i : data_memory_array_in_t;
  signal dataMemory_o : data_memory_array_out_t;
  signal boxMemory_i  : box_memory_in_t;
  signal boxMemory_o  : box_memory_out_t;
  signal dotList_i    : list_array_in_t;
  signal dotList_o    : list_array_out_t;
  signal fetch_o      : fetch_out_t;
  signal fetch_i      : fetch_in_t;
  signal load_o       : load_out_t;
  signal load_i       : load_in_t;
  signal calc_o       : calc_out_t;
  signal calc_i       : calc_in_t;
  signal writeBack_o  : write_back_out_t;
  signal writeBack_i  : write_back_in_t;

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
  fetch_c : fetch_stage
    port map(
      clk     => clk,
      reset_n => mu_monitor_reset_n,
      i       => fetch_i,
      o       => fetch_o
      );

  load_c : load_stage
    port map(
      clk     => clk,
      reset_n => mu_monitor_reset_n,
      i       => load_i,
      o       => load_o
      );

  calc_c : calc_stage
    port map(
      clk     => clk,
      reset_n => mu_monitor_reset_n,
      i       => calc_i,
      o       => calc_o
      );

  writeBack_c : write_back_stage
    port map(
      clk     => clk,
      reset_n => mu_monitor_reset_n,
      i       => writeBack_i,
      o       => writeBack_o
      );

  -- data memory
  generate_data_memory : for i in 0 to 1 generate
    dataMemory_c : dp_ram_1w_3r_wt
      generic map(
        ADDR_WIDTH => log2c(ROM_LEN),
        DATA_WIDTH => 1
        )
      port map(
        clk        => clk,
        rdAddrA    => dataMemory_i(i).rdAddrA,
        rdAddrB    => dataMemory_i(i).rdAddrB,
        rdAddrC    => dataMemory_i(i).rdAddrC,
        rdDataA(0) => dataMemory_o(i).rdDataA,
        rdDataB(0) => dataMemory_o(i).rdDataB,
        rdDataC(0) => dataMemory_o(i).rdDataC,
        wrAddr     => dataMemory_i(i).wrAddr,
        wrData(0)  => dataMemory_i(i).wrData,
        write      => dataMemory_i(i).write
        );
  end generate;

  -- box memory
  boxMemory_c : sp_ram_wt
    generic map(
      ADDR_WIDTH => log2c(BOX_MEMORY_LEN),
      DATA_WIDTH => TIMESTAMP_T_WIDTH
      )
    port map (
      clk    => clk,
      addr   => boxMemory_i.rdAddr,
      wrData => boxMemory_i.wrData,
      write  => boxMemory_i.write,
      rdData => boxMemory_o.rdData
      );

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

  -- dot memory
  dot_memory_c : list_array
    generic map(
      BUFFER_SIZE    => 256,
      DOT_BUFFER_LEN => DOT_BUFFER_LEN
      )
    port map(
      clk   => clk,
      res_n => reset_n,
      i     => dotList_i,
      o     => dotList_o
      );
      
  -- logic
  cominatorial : process(this, dataMemory_i, dataMemory_o, boxMemory_i, boxMemory_o, dotList_i, dotList_o, fetch_o, fetch_i, load_o, load_i, calc_o, calc_i, writeBack_o, writeBack_i, atomics, timestamp, imemRdData, intMemRdData, reset_n, en, program_imem, program_interval_memory, program_addr, program_data, data_memory_addr)
    variable nxt         : registerType;
    variable preMemory_i : data_memory_in_t;
    variable preMemory_o : data_memory_out_t;
    variable nowMemory_i : data_memory_in_t;
    variable nowMemory_o : data_memory_out_t;
  begin
    nxt := this;

    mu_monitor_reset_n <= not ((not reset_n) or (not en));  -- low active reset signal

    -- program memories
    imemWrAddr <= program_addr(log2c(ROM_LEN) - 1 downto 0);
    imemWrData <= program_data(COMMAND_WIDTH-1 downto 0);
    imemWrite  <= program_imem;

    intMemWrAddr <= program_addr(log2c(INTERVAL_MEMORY_LEN) - 1 downto 0);
    intMemWrData <= program_data(2*TIMESTAMP_WIDTH-1 downto 0);
    intMemWrite  <= program_interval_memory;

    preMemory_i.wrAddr := (others => '0');
    preMemory_i.wrData := '0';
    preMemory_i.write  := '0';

    -- select data memory
    if this.memory_select = '0' then
      preMemory_o := dataMemory_o(0);
      nowMemory_o := dataMemory_o(1);
    else
      preMemory_o := dataMemory_o(1);
      nowMemory_o := dataMemory_o(0);
    end if;

	data_memory_data <= nowMemory_o.rdDataC;
	finish <= calc_o.calc_finish;

    -- fetch stage 
    fetch_i.start   <= '0';
    fetch_i.memData <= imemRdData;
    fetch_i.nxt_ack <= load_o.ack;
    imemRdAddr      <= fetch_o.memAddr;

    -- load stage
    load_i.atomics              <= this.atomics;
    load_i.last_atomics         <= this.last_atomics;
    load_i.calcFin              <= calc_o.fin;
    load_i.calc_idle            <= calc_o.idle;
    load_i.calc_result          <= calc_o.resultNow;
    load_i.initialized          <= calc_o.initialized;
    load_i.interval_memory_data <= intMemRdData;
    load_i.nxt_ack              <= calc_o.ack;
    load_i.prev_fin             <= fetch_o.fin;
    load_i.reg                  <= fetch_o.reg;
    load_i.preMemory            <= preMemory_o;
    load_i.nowMemory            <= nowMemory_o;
    intMemRdAddr                <= load_o.interval_memory_addr;
    preMemory_i.rdAddrA         := load_o.preMemory.rdAddrA;
    preMemory_i.rdAddrB         := load_o.preMemory.rdAddrB;
    preMemory_i.rdAddrC         := load_o.preMemory.rdAddrC;
    nowMemory_i.rdAddrA         := load_o.nowMemory.rdAddrA;
    nowMemory_i.rdAddrB         := load_o.nowMemory.rdAddrB;
    nowMemory_i.rdAddrC         := load_o.nowMemory.rdAddrC;


    -- calc stage
    calc_i.dotMemory <= dotList_o;
    calc_i.boxMemory <= boxMemory_o;
    calc_i.nxt_ack   <= writeBack_o.ack;
    calc_i.prev_fin  <= load_o.fin;
    calc_i.time      <= this.time;
    calc_i.reg       <= load_o.reg;
    dotList_i        <= calc_o.dotMemory;
    boxMemory_i      <= calc_o.boxMemory;
    violated         <= calc_o.violated;
    valid            <= not calc_o.violated;
    violated_valid   <= calc_o.violated_valid;

    dotList_i.fetch_buffer_nr <= load_o.buffer_nr;

    -- write back stage
    writeBack_i.prev_fin <= calc_o.fin;
    writeBack_i.reg      <= calc_o.reg;
    nowMemory_i.wrAddr   := writeBack_o.nowMemory.wrAddr;
    nowMemory_i.wrData   := writeBack_o.nowMemory.wrData;
    nowMemory_i.write    := writeBack_o.nowMemory.write;

    if en = '1' then
      if this.time /= timestamp then    -- new cycle
        fetch_i.start     <= '1';
        nxt.time          := timestamp;
        nxt.last_atomics  := this.atomics;
        nxt.atomics       := atomics;
        nxt.memory_select := not this.memory_select;
        nxt.forward_data_mem := '0';
      end if;
    end if;
    
    if calc_o.calc_finish = '1' then
        nxt.forward_data_mem := '1';
    end if;

	if this.forward_data_mem = '1' then
	    nowMemory_i.rdAddrC := data_memory_addr;
	end if;

    -- select data memory
    if this.memory_select = '0' then
      dataMemory_i(0) <= preMemory_i;
      dataMemory_i(1) <= nowMemory_i;
    else
      dataMemory_i(1) <= preMemory_i;
      dataMemory_i(0) <= nowMemory_i;
    end if;

    this_nxt <= nxt;
  end process;

  reg : process (clk , reset_n)
  begin
    if reset_n = '0' then
      this <= registerReset;
    elsif rising_edge (clk) then
      this <= this_nxt;
    end if;
  end process;

end architecture;
