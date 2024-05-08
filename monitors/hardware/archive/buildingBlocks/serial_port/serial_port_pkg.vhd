----------------------------------------------------------------------------------
-- Company:      TU Wien - ECS Group                                            --
-- Engineer:     Thomas Polzer                                                  --
--                                                                              --
-- Create Date:  21.09.2010                                                     --
-- Design Name:  DIDELU                                                         --
-- Module Name:  serial_port_pkg                                                --
-- Project Name: DIDELU                                                         --
-- Description:  Serial - Package                                               --
----------------------------------------------------------------------------------

----------------------------------------------------------------------------------
--                                LIBRARIES                                     --
----------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;


----------------------------------------------------------------------------------
--                                 PACKAGE                                      --
----------------------------------------------------------------------------------

package serial_port_pkg is

   --constant CLK_FREQ : integer := 100000000;
   constant BAUD_RATE : integer := 115200;
   constant SYNC_STAGES : integer := 3;
   constant TX_FIFO_DEPTH : integer := 4096;
   constant RX_FIFO_DEPTH : integer := 156;
  --------------------------------------------------------------------
  --                          COMPONENT                             --
  --------------------------------------------------------------------

  -- connection between transmitter and receiver
  component serial_port is
    generic
    (
      -- clock frequency [Hz]
      CLK_FREQ : integer;
      -- transmission baud rate
      BAUD_RATE : integer;
      -- number o stages in the input synchronizer
      SYNC_STAGES : integer;
      -- depth of the tx fifo
      TX_FIFO_DEPTH : integer;
      -- depth of the rx fifo
      RX_FIFO_DEPTH : integer
    );
    port
    (
      clk, res_n         : in  std_logic;

      tx_data            : in  std_logic_vector(7 downto 0);
      tx_wr              : in  std_logic;
      tx_free            : out std_logic;
          
      rx_data            : out std_logic_vector(7 downto 0);
      rx_rd              : in  std_logic;
      rx_data_empty      : out std_logic;
      rx_data_full       : out std_logic;

      rx                 : in  std_logic;
      tx                 : out std_logic
    );
  end component serial_port;

  -- serial receiver
  component serial_port_receiver is
    generic
    (
      CLK_DIVISOR : integer
    );
    port
    (
      clk, res_n         : in  std_logic;

      data               : out std_logic_vector(7 downto 0);
      data_new           : out std_logic;

      rx                 : in  std_logic
    );
  end component serial_port_receiver;

  -- serial transmitter
  component serial_port_transmitter is
    generic
    (
      CLK_DIVISOR : integer
    );
    port
    (
      clk, res_n         : in  std_logic;

      data               : in  std_logic_vector(7 downto 0);
      empty              : in  std_logic;
      rd                 : out std_logic;
      
      tx                 : out std_logic
    );
  end component serial_port_transmitter;
end serial_port_pkg;

--- EOF ---
