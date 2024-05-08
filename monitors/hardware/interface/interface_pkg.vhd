-------------------------------------------------------------------------------
-- Project    : R2U2 (Realizable Responsive Unobtrusive Unit)
-------------------------------------------------------------------------------
-- File       : interface_pkg.vhd
-------------------------------------------------------------------------------
-- Description:  Package for interface components.                    
------------------------------------------------------------------------------- 

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

package interface_pkg is

component echo
port
(
  clk        : in std_logic;
  reset      : in std_logic;
  data_in    : in std_logic_vector (7 downto 0); -- data received
  data_out   : out std_logic_vector (7 downto 0); -- data to transmit
  RX_full   : in std_logic; -- Indicate UART is ready to receive data
  TX_ready   : in std_logic; -- Indicate UART is ready for data to transmit
  read       : out std_logic; -- Read a byte from the UART
  write      : out std_logic; -- Write a byte to the UART
  soft_reset : out std_logic;
  pRBUS_DATA : in std_logic_vector(15 downto 0);
  pRBUS_ADDR : in std_logic_vector(7 downto 0);
  pRBUS_EN   : in std_logic;
  LD0        : out std_logic;
  LD1        : out std_logic;
  LD2        : out std_logic       
);
end component;

component process_data
generic(
    rtc_divid : integer range 2 to 200000000 := 25000000 
);
port
(
  clk        : in std_logic;
  reset      : in std_logic;
  new_data   : in std_logic; -- Indicate a new byte (data_in) has been captured from UART
  data_in    : in std_logic_vector (7 downto 0); -- Data from the UART
  send_data  : out std_logic; -- Request UART to transmit data_out
  data_out   : out std_logic_vector (7 downto 0);  -- Data to send to the UART
  soft_reset : out std_logic;
  pRBUS_DATA : in std_logic_vector(15 downto 0);
  pRBUS_ADDR : in std_logic_vector(7 downto 0);
  pRBUS_EN   : in std_logic;
  LD0        : out std_logic;
  LD1        : out std_logic;
  LD2        : out std_logic
);
end component;

end package;

package body interface_pkg is

end package body;
