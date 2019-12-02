library ieee;
use ieee.std_logic_1164.all;
use work.serial_port_pkg.all;
use work.testbench_util_pkg.all;

entity serial_port_tb is
end serial_port_tb;

architecture sim of serial_port_tb is
  constant CLK_PERIODE : time    := 10 ns;
  constant CLK_FREQ    : integer := 100000000;
  constant BAUD_RATE   : integer := 115200;

  signal clk, nres          : std_logic := '0';
  signal data_in            : std_logic_vector(7 downto 0) := (others => '0');
  signal wr, free, finished : std_logic := '0';
  signal data_out           : std_logic_vector(7 downto 0) := (others => '0');
  signal new_data           : std_logic := '0';
  signal rx, tx             : std_logic := '0';
  signal rx_data_empty      : std_logic;
  signal rx_data_full       : std_logic;
  
begin
  serial_port_1 : serial_port
    generic map (
      CLK_FREQ      => CLK_FREQ,
      BAUD_RATE     => BAUD_RATE,
      SYNC_STAGES   => 5,
      TX_FIFO_DEPTH => 4,
      RX_FIFO_DEPTH => 4)
    port map (
      clk           => clk,
      res_n         => nres,
      tx_data       => data_in,
      tx_wr         => wr,
      tx_free       => free,
      rx_data       => data_out,
      rx_rd         => new_data,
      rx_data_empty => rx_data_empty,
      rx_data_full  => rx_data_full,
      rx            => rx,
      tx            => tx);

  rx <= tx;

  process
  begin
    clk <= '0';
    wait for CLK_PERIODE / 2;
    clk <= '1';
    wait for CLK_PERIODE / 2;
  end process;

  process
  begin
    nres    <= '0';
    wait_cycle(clk, 10);
    nres    <= '1';
    data_in <= x"55";
    wr      <= '1';
    wait_cycle(clk, 1);
    wr      <= '0';
    wait until free = '1';
    data_in <= x"AA";
    wr      <= '1';
    wait_cycle(clk, 1);
    wr      <= '0';
    wait until free = '1';
    data_in <= x"00";
    wr      <= '1';
    wait_cycle(clk, 1);
    wr      <= '0';
    wait until finished = '1';
    data_in <= x"FF";
    wr      <= '1';
    wait_cycle(clk, 1);
    wr      <= '0';
    wait until finished = '1';
  end process;
  
end sim;
