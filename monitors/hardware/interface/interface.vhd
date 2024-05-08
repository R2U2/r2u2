-------------------------------------------------------------------------------
-- Project    : R2U2 (Realizable Responsive Unobtrusive Unit)
-------------------------------------------------------------------------------
-- File       : interface.vhd
-------------------------------------------------------------------------------
-- Description:  Main interface file: Process data received from the UART and
--Echo data recived from the UART back to the PC                                      echo back to the PC               
------------------------------------------------------------------------------- 
library IEEE;
use IEEE.std_logic_1164.all;
use ieee.numeric_std.all;

use work.interface_pkg.all;
use work.uart_pkg.all;


entity interface is
port
(
  sysclk    : in  std_logic;
  reset : in  std_logic;
  FPGA_SERIAL1_TX  : out std_logic;
  FPGA_SERIAL1_RX  : in  std_logic;
  pRBUS_DATA : in std_logic_vector(15 downto 0);
  pRBUS_ADDR : in std_logic_vector(7 downto 0);
  pRBUS_EN : in std_logic;
  LD0 : out std_logic;
  LD1 : out std_logic;
  LD2 : out std_logic
);  
end interface;

architecture rtl of interface is

signal reset_out     : std_logic;  -- Reset active high
 
signal DIN   : std_logic_vector(7 downto 0);  -- Data to Transmit
signal DIN_VLD : std_logic; -- Data to transmit is valid
signal DIN_RDY : std_logic; -- Transmitter is ready
signal DOUT  : std_logic_vector(7 downto 0);  -- Data Recieved
signal DOUT_VLD : std_logic; -- Data received is valid
  
signal soft_reset : std_logic;
signal cnt : std_logic_vector(31 downto 0);
signal start_cnt : std_logic;

signal data_in_reg : std_logic_vector(7 downto 0); -- Temp store incoming data
signal data_to_send : std_logic_vector(7 downto 0); -- Temp store outgoing data

signal new_data_reg : std_logic;
signal send_data : std_logic;

begin


soft_reset_process : process(sysclk,reset)
begin
  if(sysclk='1' and sysclk'event)then
    if(reset='1') then
      cnt <= (others=>'0');
      start_cnt <= '0';
      reset_out <= '1';
    else
      reset_out <= '0';
      if(soft_reset='1')then
        start_cnt <= '1';
      end if;
      if(start_cnt='1')then
        if(unsigned(cnt)<102129222)then -- reset signal should longer than 1 sample period??
          cnt <= std_logic_vector(unsigned(cnt)+1);
          reset_out <= '1';
        else
          start_cnt <= '0';
          reset_out <= '0';
          cnt <= (others=>'0');
        end if;
      end if; 
    end if;
  end if;
end process;

receive_data : process(sysclk)
begin
  if(sysclk'event and sysclk = '1') then
    if(reset = '1') then
      new_data_reg   <= '0';
      data_in_reg    <= (others => '0');
    else    
      if(DOUT_VLD = '1') then -- check if a new byte has arrived
        new_data_reg   <= '1';
        data_in_reg <= DOUT;
      else
        new_data_reg   <= '0';
        data_in_reg <= data_in_reg;
      end if;	 
    end if;
  end if;

end process;

send_data_process : process(sysclk)
begin
  if(sysclk'event and sysclk = '1') then
    if(reset = '1') then
      DIN_VLD <= '0';
    else
      if(send_data = '1' and DIN_RDY = '1') then -- lower level component has a byte to send
        -- wait until DIN_RDY = '1';
        DIN <= data_to_send; -- data to transmit
        DIN_VLD <= '1'; -- data to transmit is valid
      else
        DIN_VLD <= '0';
      end if;	 
    end if;
  end if;

end process;

UART_1 : UART
generic map(
    CLK_FREQ => 500e6,   -- 500 MHz MHz frequency
    BAUD_RATE => 115200, -- 115200 baud rate
    PARITY_BIT => "none", -- no parity
    USE_DEBOUNCER => True    -- enable debouncer
)
port map(
    -- CLOCK AND RESET
    CLK => sysclk, -- system clock
    RST => reset, -- high active synchronous reset
    -- UART INTERFACE
    UART_TXD => FPGA_SERIAL1_TX, -- serial transmit data
    UART_RXD => FPGA_SERIAL1_RX, -- serial receive data
    -- USER DATA INPUT INTERFACE
    DIN => DIN, -- input data to be transmitted over UART
    DIN_VLD => DIN_VLD, -- when DIN_VLD = 1, input data (DIN) are valid
    DIN_RDY => DIN_RDY, -- when DIN_RDY = 1, transmitter is ready and valid input data will be accepted for transmiting
    -- USER DATA OUTPUT INTERFACE
    DOUT => DOUT, -- output data received via UART
    DOUT_VLD => DOUT_VLD, -- when DOUT_VLD = 1, output data (DOUT) are valid (is assert only for one clock cycle)
    FRAME_ERROR => open,
    PARITY_ERROR => open
);

process_data_1 : process_data
port map
( 
  clk       => sysclk,
  reset     => reset_out,
  new_data  => new_data_reg,
  data_in   => data_in_reg,
  send_data => send_data,
  data_out  => data_to_send,
  soft_reset => soft_reset,
  pRBUS_DATA => pRBUS_DATA,
  pRBUS_ADDR => pRBUS_ADDR,
  pRBUS_EN => pRBUS_EN, 
  LD0 => LD0,
  LD1 => LD1,
  LD2 => LD2
);

end rtl;
