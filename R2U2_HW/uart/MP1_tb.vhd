-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
--                                                                           --
-- File Name: MP1_tb.vhd                                                     --
-- Author: Phillip Jones (phjones@iastate.edu  )                             --
-- Date: 8/27/2010                                                           --
--                                                                           --
-- Description: Testbench for MP1_top: An UART echo circuit                      --
--                                                                           --
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.STD_LOGIC_ARITH.ALL;
use IEEE.STD_LOGIC_UNSIGNED.ALL;
use std.textio.all;
use work.uart_pkg.all;

entity MP1_tb is
generic(
uartFilePath  : string := "/home/pei/Documents/github/SystemHealthManagement/R2U2/R2U2-HW/demo/scripts/send.uart"
);
port
(
my_in : in std_logic -- input need to keep modelsim from                        
                     -- compaining???
);
end MP1_tb;

architecture rtl of MP1_tb is

----------------------------------------------
--       Component declarations             --
----------------------------------------------

-- Component that get put on the FPGA
component MP1_top
port
(
  sysclk    : in  std_logic;  -- system clock
  RESET_low : in  std_logic;  -- Active low
  FPGA_SERIAL1_TX  : out std_logic;
  FPGA_SERIAL1_RX  : in  std_logic
);
end component;


-- Component used to send test data to
-- MP1_top for testing before placing
-- MP1_top on the FPGA
component MP1_top_driver
port
(
  sysclk    : in  std_logic;  -- system clock
  RESET_low : in  std_logic;  -- Active low
  FPGA_SERIAL1_TX  : out std_logic;
  FPGA_SERIAL1_RX  : in  std_logic;
  Send_Data_array : in TEST_DATA_type
);
end component;

file uart_file : text open read_mode is uartFilePath;
----------------------------------------------
--          Signal declarations             --
----------------------------------------------
signal system_clk : std_logic;  -- system clock
signal reset_n    : std_logic;  -- Reset active low

signal TX_driver : std_logic;   -- Byte of Data to Ready to read
signal RX_driver : std_logic;   -- Active low indicate busy transmitting
signal data_array : TEST_DATA_type := (others=>(others=>'0'));

begin


-- Processes

-------------------------------------------
-------------------------------------------
-- Process Name: system_clk_gen          --
--                                       --
-- Description: Generat clock to run the --
-- simulation.                           --
--                                       --
--                                       --
-------------------------------------------
-------------------------------------------  
system_clk_gen : process
begin
  system_clk <= '0';
  wait for 10 ns;
    loop
      wait for 1 ns;
      system_clk <= '1';
      wait for 1 ns;
      system_clk <= '0';
    end loop;
end process system_clk_gen;


-------------------------------------------
-------------------------------------------
-- Process Name: toggle_reset            --
--                                       --
-- Description: Generat clock to run the --
-- simulation.                           --
--                                       --
--                                       --
-------------------------------------------
-------------------------------------------  
toggle_reset : process
begin
  reset_n <= '1'; -- place circuit in reset
  wait for 100 ns;
  reset_n <= '0'; 
  wait;
end process toggle_reset;


read_input : process
variable v_file_line_rd    : line;
variable v_str_line        : string (8 downto 1);
variable I : integer := 0;
begin
    while (not endfile(uart_file)) and I<data_size-1  loop
      readline(uart_file, v_file_line_rd);
      read(v_file_line_rd, v_str_line);
      data_array(I) <= str_to_std_logic_vector(v_str_line);
      I := I+1;
    end loop;
    wait;
end process;


-- Combinational assignments


  -- Port map MP1_top_driver
UART_driver : MP1_top_driver  
port map
(
  sysclk          =>  system_clk,  -- system clock
  RESET_low       =>  reset_n,     -- Active low reset
  FPGA_SERIAL1_TX =>  TX_driver,   -- Serial driver transmit 
  FPGA_SERIAL1_RX =>  RX_driver,    -- Serial driver recieve
  Send_Data_array =>  data_array
);


  -- Port map MP1_top
UART_HW : MP1_top  
port map
(
  sysclk          =>  system_clk,  -- system clock
  RESET_low       =>  reset_n,     -- Active low reset
  FPGA_SERIAL1_TX =>  RX_driver,   -- Send data to MP1_top_driver recieve 
  FPGA_SERIAL1_RX =>  TX_driver    -- Get data from MP1_top_driver transmit
);



end rtl;
