-------------------------------------------------------------------------------
-- Project    : R2U2 (Realizable Responsive Unobtrusive Unit)
-------------------------------------------------------------------------------
-- File       : uart_pkg.vhd
-------------------------------------------------------------------------------
-- Description:  Package for uart components.                    
------------------------------------------------------------------------------- 

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

package uart_pkg is

component UART is
generic (
    CLK_FREQ      : integer := 50e6;   -- system clock frequency in Hz
    BAUD_RATE     : integer := 115200; -- baud rate value
    PARITY_BIT    : string  := "none"; -- type of parity: "none", "even", "odd", "mark", "space"
    USE_DEBOUNCER : boolean := True    -- enable/disable debouncer
);
port (
    -- CLOCK AND RESET
    CLK          : in  std_logic; -- system clock
    RST          : in  std_logic; -- high active synchronous reset
    -- UART INTERFACE
    UART_TXD     : out std_logic; -- serial transmit data
    UART_RXD     : in  std_logic; -- serial receive data
    -- USER DATA INPUT INTERFACE
    DIN          : in  std_logic_vector(7 downto 0); -- input data to be transmitted over UART
    DIN_VLD      : in  std_logic; -- when DIN_VLD = 1, input data (DIN) are valid
    DIN_RDY      : out std_logic; -- when DIN_RDY = 1, transmitter is ready and valid input data will be accepted for transmiting
    -- USER DATA OUTPUT INTERFACE
    DOUT         : out std_logic_vector(7 downto 0); -- output data received via UART
    DOUT_VLD     : out std_logic; -- when DOUT_VLD = 1, output data (DOUT) are valid (is assert only for one clock cycle)
    FRAME_ERROR  : out std_logic; -- when FRAME_ERROR = 1, stop bit was invalid (is assert only for one clock cycle)
    PARITY_ERROR : out std_logic  -- when PARITY_ERROR = 1, parity bit was invalid (is assert only for one clock cycle)
);
end component;

end package;

package body uart_pkg is

end package body;
