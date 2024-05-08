-------------------------------------------------------------------------------
-- Project    : CevTes RVU (Runtime Verification Unit)
-------------------------------------------------------------------------------
-- File       : list_array.vhd
-- Author     : Andreas Hagmann (ahagmann@ecs.tuwien.ac.at)
-- Copyright  : 2012, Thomas Reinbacher (treinbacher@ecs.tuwien.ac.at)
--              Vienna University of Technology, ECS Group
-------------------------------------------------------------------------------
-- Description: implements a array of lists for dot operators
-------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pkg.all;
use work.mu_monitor_pkg.all;
use work.cevlib_unsigned_pkg.all;
use work.ram_pkg.all;

entity list_array is
  generic (
    BUFFER_SIZE    : integer;           -- must be power of 2
    DOT_BUFFER_LEN : integer
    );
  port (
    clk   : in  std_logic;              -- clock signal
    res_n : in  std_logic;
    i     : in  list_array_in_t;
    o     : out list_array_out_t
    );
end entity;

architecture beh of list_array is

  type register_t is record
    buffer_nr         : std_logic_vector(log2c(DOT_BUFFER_LEN) - 1 downto 0);
    readP             : std_logic_vector(log2c(BUFFER_SIZE) - 1 downto 0);  -- read pointer
    writeP            : std_logic_vector(log2c(BUFFER_SIZE) - 1 downto 0);  -- write pointer
    fetch_read_p      : std_logic_vector(log2c(BUFFER_SIZE) - 1 downto 0);  -- read pointer
    fetch_write_p     : std_logic_vector(log2c(BUFFER_SIZE) - 1 downto 0);  -- write pointer
    tail_element      : timestampTuple_t;
    head_element      : timestampTuple_t;
    data_memory_write : std_logic;
    tail_memory_write : std_logic;
  end record;

  -- check: remove types and use separate signals
  type pointerMemoryControl_t is record
    rdAddr : std_logic_vector(log2c(DOT_BUFFER_LEN) - 1 downto 0);  -- read address
    wrAddr : std_logic_vector(log2c(DOT_BUFFER_LEN) - 1 downto 0);  -- read address
    wrData : std_logic_vector(log2c(BUFFER_SIZE)*2 - 1 downto 0);  -- write data
    write  : std_logic;
  end record;

  type dataMemoryControl_t is record
    rdAddr : std_logic_vector(log2c(DOT_BUFFER_LEN * BUFFER_SIZE) - 1 downto 0);  -- read address
    wrAddr : std_logic_vector(log2c(DOT_BUFFER_LEN * BUFFER_SIZE) - 1 downto 0);  -- read address
    wrData : std_logic_vector(INTERVAL_T_WIDTH - 1 downto 0);  -- write data
    write  : std_logic;
  end record;

  type tailMemoryControl_t is record
    addr   : std_logic_vector(log2c(DOT_BUFFER_LEN) - 1 downto 0);  -- read address
    wrData : std_logic_vector(TIMESTAMPTUPLE_T_WIDTH - 1 downto 0);  -- write data
    write  : std_logic;
  end record;

  constant registerReset : register_t := (
  (std_logic_vector(to_unsigned(0,log2c(DOT_BUFFER_LEN)))),--(others => '0'),
  (std_logic_vector(to_unsigned(0,log2c(BUFFER_SIZE)))),--(others => '0'),
  (std_logic_vector(to_unsigned(0,log2c(BUFFER_SIZE)))),--(others => '0'),
  (std_logic_vector(to_unsigned(0,log2c(BUFFER_SIZE)))),--(others => '0'),
  (std_logic_vector(to_unsigned(0,log2c(BUFFER_SIZE)))),--(others => '0'),
  --  (others => '0'),
  --  (others => '0'),
  --  (others => '0'),
  --  (others => '0'),
    TIMESTAMPTUPLE_T_NULL,
    TIMESTAMPTUPLE_T_NULL,
    '0',
    '0'
    );

  signal this, this_nxt       : register_t := registerReset;
  signal pointerMemoryControl : pointerMemoryControl_t;
  signal pointerMemoryData    : std_logic_vector(log2c(BUFFER_SIZE)*2 - 1 downto 0);
  signal dataMemoryControl    : dataMemoryControl_t;
  signal dataMemoryData       : std_logic_vector(INTERVAL_T_WIDTH - 1 downto 0);
  signal tailMemoryControl    : tailMemoryControl_t;
  signal tailMemoryData       : std_logic_vector(TIMESTAMPTUPLE_T_WIDTH - 1 downto 0);


begin

  -- instantiate components
  pointer_memory_inst : dp_ram
    generic map(
      ADDR_WIDTH => log2c(DOT_BUFFER_LEN),
      DATA_WIDTH => log2c(BUFFER_SIZE) * 2
      )
    port map(
      clk    => clk,
      rdAddr => pointerMemoryControl.rdAddr,
      wrAddr => pointerMemoryControl.wrAddr,
      wrData => pointerMemoryControl.wrData,
      write  => pointerMemoryControl.write,
      rdData => pointerMemoryData
      );

  data_memory_inst : dp_ram             -- check: do we need the dp ram
    generic map(
      ADDR_WIDTH => log2c(DOT_BUFFER_LEN * BUFFER_SIZE),
      DATA_WIDTH => INTERVAL_T_WIDTH
      )
    port map(
      clk    => clk,
      rdAddr => dataMemoryControl.rdAddr,
      wrAddr => dataMemoryControl.wrAddr,
      wrData => dataMemoryControl.wrData,
      write  => dataMemoryControl.write,
      rdData => dataMemoryData
      );

  tail_element_memory_inst : sp_ram_wt
    generic map(
      ADDR_WIDTH => log2c(DOT_BUFFER_LEN),
      DATA_WIDTH => TIMESTAMPTUPLE_T_WIDTH
      )
    port map(
      clk    => clk,
      addr   => tailMemoryControl.addr,
      wrData => tailMemoryControl.wrData,
      write  => tailMemoryControl.write,
      rdData => tailMemoryData
      );

  -- logic

  combinatorial : process (this, i, pointerMemoryData, tailMemoryData, dataMemoryData)
    variable nxt        : register_t;
    variable emptyLocal : std_logic;
  begin
    nxt := this;

    --nxt.readP := pointerMemoryData(log2c(BUFFER_SIZE)*2 - 1 downto log2c(BUFFER_SIZE));
    --nxt.writeP := pointerMemoryData(log2c(BUFFER_SIZE) - 1 downto 0);
    nxt.tail_element := slv_to_tst(tailMemoryData);

    -- defaults
    pointerMemoryControl.write <= '0';
    nxt.data_memory_write      := '0';
    dataMemoryControl.write    <= this.data_memory_write;
    nxt.tail_memory_write      := '0';
    tailMemoryControl.write    <= this.tail_memory_write;
    nxt.fetch_read_p           := pointerMemoryData(log2c(BUFFER_SIZE)*2 - 1 downto log2c(BUFFER_SIZE));
    nxt.fetch_write_p          := pointerMemoryData(log2c(BUFFER_SIZE) - 1 downto 0);

    dataMemoryControl.rdAddr <= this.buffer_nr & this.readP;

    if this.readP = this.writeP then
      emptyLocal := '1';
    else
      emptyLocal := '0';
    end if;

    -- output
    o.empty <= emptyLocal;
    o.tail  <= this.tail_element;
    if emptyLocal = '1' then
      nxt.head_element := this.tail_element;
    else
      nxt.head_element.start.time  := dataMemoryData(2*TIMESTAMP_WIDTH - 1 downto TIMESTAMP_WIDTH);
      nxt.head_element.stop.time   := dataMemoryData(TIMESTAMP_WIDTH - 1 downto 0);
      nxt.head_element.start.valid := '1';
      nxt.head_element.stop.valid  := '1';
    end if;

    o.head <= this.head_element;

    -- actions to control signals

    if i.sel = '1' then
      nxt.buffer_nr            := i.buffer_nr;
      nxt.readP                := this.fetch_read_p;
      nxt.writeP               := this.fetch_write_p;
      dataMemoryControl.rdAddr <= i.buffer_nr & this.fetch_read_p;
    end if;

    if i.add_start = '1' then
      nxt.tail_element.start.valid := '1';
      nxt.tail_element.start.time  := i.timestamp;
      nxt.tail_element.stop.valid  := '0';

      nxt.tail_memory_write := '1';
    end if;

    if i.add_end = '1' then
      nxt.tail_element.stop.valid := '1';
      nxt.tail_element.stop.time  := i.timestamp;

      nxt.tail_memory_write := '1';
      nxt.data_memory_write := '1';

      if emptyLocal = '1' then
        nxt.head_element := nxt.tail_element;  -- forward data to head_element, so it is valid in the nxt cycle
      end if;
    end if;

    if i.delete = '1' then  -- this assumes that at least on element is in the buffer
      nxt.readP                  := this.readP + 1;
      pointerMemoryControl.write <= '1';
    end if;

    if i.set_tail = '1' then
      nxt.tail_element.start.valid := '1';
      nxt.tail_element.start.time  := (others => '0');
      nxt.tail_element.stop.valid  := '1';
      nxt.tail_element.stop.time   := i.timestamp;

      nxt.head_element := nxt.tail_element;  -- forward data to head_element, so it is valid in the nxt cycle

      nxt.readP := this.writeP;

      pointerMemoryControl.write <= '1';
      nxt.tail_memory_write      := '1';
      nxt.data_memory_write      := '1';
    end if;

    if i.reset_tail = '1' then
      nxt.readP := this.writeP;         -- clear memory

      nxt.tail_element.start.valid := '1';
      nxt.tail_element.start.time  := (others => '0');
      nxt.tail_element.stop.valid  := '0';

      nxt.head_element := nxt.tail_element;  -- forward data to head_element, so it is valid in the nxt cycle

      pointerMemoryControl.write <= '1';
      nxt.tail_memory_write      := '1';
    end if;

    if i.drop_tail = '1' then
      nxt.tail_element.start.valid := '0';
      nxt.tail_element.stop.valid  := '0';

      nxt.tail_memory_write := '1';
    end if;


    if this.data_memory_write = '1' then
      nxt.writeP                 := this.writeP + 1;
      pointerMemoryControl.write <= '1';
    end if;

    -- write memories

    tailMemoryControl.wrData <= tst_to_slv(this.tail_element);
    tailMemoryControl.addr   <= this.buffer_nr;

    pointerMemoryControl.wrData <= nxt.readP & nxt.writeP;
    pointerMemoryControl.wrAddr <= nxt.buffer_nr;
    pointerMemoryControl.rdAddr <= i.fetch_buffer_nr;

    dataMemoryControl.wrData <= this.tail_element.start.time & this.tail_element.stop.time;
    dataMemoryControl.wrAddr <= this.buffer_nr & this.writeP;

    this_nxt <= nxt;
  end process;

  reg : process (clk , res_n)
  begin
    if res_n = '0' then
      this <= registerReset;
    elsif rising_edge (clk) then
      this <= this_nxt;
    end if;
  end process;

end architecture;
