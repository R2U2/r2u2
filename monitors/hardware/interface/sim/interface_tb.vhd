-------------------------------------------------------------------------------
-- Project    : R2U2 (Realizable Responsive Unobtrusive Unit)
-------------------------------------------------------------------------------
-- File       : interface_tb.vhd
-------------------------------------------------------------------------------
-- Description:  Testbench for interface.                    
------------------------------------------------------------------------------- 
library IEEE;
use IEEE.std_logic_1164.all;
use ieee.numeric_std.all;
use std.textio.all;
use work.testbench_util_pkg.all;
use work.uart_pkg.all;

entity interface_tb is
generic(
uartFilePath  : string := "PATH_TO_DIRECTORY/r2u2/tools/preprocessing/send.uart"
);
end interface_tb;

architecture rtl of interface_tb is

component interface is
port
(
  sysclk    : in  std_logic;  -- system clock
  reset : in  std_logic;  -- Active low (but polarity is immediate made active high)
  FPGA_SERIAL1_TX  : out std_logic;
  FPGA_SERIAL1_RX  : in  std_logic;
  pRBUS_DATA : in std_logic_vector(15 downto 0);
  pRBUS_ADDR : in std_logic_vector(7 downto 0);
  pRBUS_EN : in std_logic;
  LD0 : out std_logic;
  LD1 : out std_logic;
  LD2 : out std_logic
);  
end component;

file uart_file : text open read_mode is uartFilePath;

signal system_clk : std_logic;  -- system clock
signal reset    : std_logic;  -- reset
signal clk_period : time:=2 ns;

signal DIN   : std_logic_vector(7 downto 0);  -- Data to Transmit
signal DIN_VLD : std_logic; -- Data to transmit is valid
signal DIN_RDY : std_logic; -- Transmitter is ready

signal DOUT : std_logic_vector(7 downto 0);  -- Data to reveive
signal DOUT_VLD : std_logic; -- Received data is valid

signal TX_driver : std_logic;
signal RX_driver : std_logic;
signal pRBUS_DATA : std_logic_vector(15 downto 0) := (others => '0');
signal pRBUS_ADDR : std_logic_vector(7 downto 0) := (others => '0');
signal pRBUS_EN : std_logic := '0';

signal config_done : boolean := false;

constant data_size: integer:=1024;--for simulation purpose
type TEST_DATA_type is array (0 to data_size-1) of std_logic_vector(7 downto 0);

signal data_array : TEST_DATA_TYPE := (others=>(others=>'0'));

begin

  system_clock_gen : process
  begin
      system_clk <= '0';
      wait for clk_period/2;
      system_clk <= '1';
      wait for clk_period/2;
  end process;

  reset_gen : process
  begin
      reset <= '1';
      wait for clk_period*10;
      reset <= '0';
      wait;
  end process;

  read_input : process
  variable v_file_line_rd    : line;
  variable v_str_line        : string (8 downto 1);
  variable I : integer := 0;
  begin
      while (not endfile(uart_file)) and I<data_size-1  loop
        readline(uart_file, v_file_line_rd);
        read(v_file_line_rd, v_str_line);
        next when v_str_line(v_str_line'length)='#';--skip the comment line
        data_array(I) <= str_to_std_logic_vector(v_str_line);
        I := I+1;
      end loop;
      config_done <= true;
      wait;
end process;

send_data_process : process
variable I : integer := 0;
begin
  wait on system_clk until reset = '0' and config_done = true;
  for I in 0 to 1024 loop
            wait on system_clk until DIN_RDY = '1'; -- Transmitter is ready to transmit byte
            DIN <= data_array(I);
            DIN_VLD <= '1';
            wait on system_clk until DIN_RDY = '0'; -- Transmitter is busy transmitting byte
  end loop;
end process;

R2U2_HW : interface
port map(
  sysclk => system_clk,  -- system clock
  reset => reset,  -- reset
  FPGA_SERIAL1_TX =>  RX_driver,
  FPGA_SERIAL1_RX =>  TX_driver,
  pRBUS_DATA => pRBUS_DATA,
  pRBUS_ADDR => pRBUS_ADDR,
  pRBUS_EN => pRBUS_EN
);  

UART_transmit : UART -- generates TX_driver_temp for RX input into interface module
generic map(
    CLK_FREQ => 500e6,   -- 500 MHz MHz frequency
    BAUD_RATE => 115200, -- 115200 baud rate
    PARITY_BIT => "none", -- no parity
    USE_DEBOUNCER => false    -- enable debouncer
)
port map(
    -- CLOCK AND RESET
    CLK => system_clk, -- system clock
    RST => reset, -- high active synchronous reset
    -- UART INTERFACE
    UART_TXD => TX_driver, -- serial transmit data
    UART_RXD => RX_driver, -- serial receive data
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

end rtl;