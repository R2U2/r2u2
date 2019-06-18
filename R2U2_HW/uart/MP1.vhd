-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
--                                                                           --
-- File Name: MP1.vhd                                                    --
-- Author: Phillip Jones (phjones@iastate.edu)                               --
-- Date: 9/2/2011                                                           --
--                                                                           --
-- Description: Top level for MP1 UART-based MP                              --
--                                                                           --
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
library IEEE;
use IEEE.std_logic_1164.all;
use ieee.numeric_std.all;


entity MP1_top is
port
(
  sysclk    : in  std_logic;  -- system clock
  RESET_low : in  std_logic;  -- Active low (but polarity is immediate made active high)
  FPGA_SERIAL1_TX  : out std_logic;
  FPGA_SERIAL1_RX  : in  std_logic;
  pRBUS_DATA : in std_logic_vector(15 downto 0);
  pRBUS_ADDR : in std_logic_vector(7 downto 0);
  pRBUS_EN : in std_logic;
  LD0 : out std_logic;
  LD1 : out std_logic;
  LD2 : out std_logic
);  
end MP1_top;

architecture rtl of MP1_top is

----------------------------------------------
--       Component declarations             --
----------------------------------------------


-- UART component: Connect the FPGA to the PC
-- over a serial (i.e. UART) cable
component mmu_uart_top
port
(
        Clk     : in std_logic;         -- main clock
        Reset_n : in std_logic;         -- main reset(phjones made active high)
        TXD     : out std_logic;        -- RS232 TX data
        RXD     : in std_logic;         -- RS232 RX data

        ck_div  : in std_logic_vector(15 downto 0);
                                        -- clock divider value
                                        -- used to get the baud rate
                                        -- baud_rate = F(clk) / (ck_div * 3)
        -- bus interface

        CE_N    : in std_logic;         -- chip enable
        WR_N    : in std_logic;         -- write enable
        RD_N    : in std_logic;         -- read enable
        A0      : in std_logic;         -- 0 - Rx/TX data reg; 1 - status reg
        D_IN    : in std_logic_vector(7 downto 0);
        D_OUT   : out std_logic_vector(7 downto 0);

        -- interrupt signals- same signals as the status register bits
        RX_full     : out std_logic;  -- Indicate a byte is ready to be ready from UART
        TX_busy_n   : out std_logic
);
end component;



-- Component that passes data to/from a 
-- subcomponent that does the actaully data processing
component process_data
port
(
  clk       : in  STD_LOGIC;
  reset     : in  STD_LOGIC;
  data_in   : in  STD_LOGIC_VECTOR (7 downto 0); -- data recived
  RX_full   : in  STD_LOGIC;  -- Indicate a byte is ready to be read from UART
  TX_busy_n : in  STD_LOGIC;  -- Active low: indicate UART is busy transmitting
  RD_n      : out  STD_LOGIC; -- Active low: read a byte from the UART
  WR_n      : out  STD_LOGIC; -- Active low: write a byte to UART for transmission
  data_out  : out  STD_LOGIC_VECTOR (7 downto 0); -- data to transmit
  soft_reset : out std_logic;
  pRBUS_DATA : in std_logic_vector(15 downto 0);
  pRBUS_ADDR : in std_logic_vector(7 downto 0);
  pRBUS_EN : in std_logic;
  LD0 : out std_logic;
  LD1 : out std_logic;
  LD2 : out std_logic       
);
end component;



----------------------------------------------
--          Signal declarations             --
----------------------------------------------
signal reset     : std_logic;  -- Reset active high
signal WR_N      : std_logic;  -- Active low write enable
signal RD_N      : std_logic;  -- Active low read enable
 
signal D_IN   : std_logic_vector(7 downto 0);  -- Data to Transmit
signal D_OUT  : std_logic_vector(7 downto 0);  -- Data Recieved


signal RX_full   : std_logic;     -- Byte of Data Ready to read
signal TX_busy_n : std_logic;     -- Active low indicate busy transmitting
  
signal soft_reset : std_logic;
signal cnt : std_logic_vector(31 downto 0);
signal start_cnt : std_logic;

begin

 

-- Combinational assignments
--reset <= not RESET_low;  -- convert to active high reset
--reset <= RESET_low;


soft_reset_process : process(sysclk,RESET_low)
begin
  if(sysclk='1' and sysclk'event)then
    if(RESET_low='1') then
      cnt <= (others=>'0');
      start_cnt <= '0';
      reset <= '1';
    else
      reset <= '0';
      if(soft_reset='1')then
        start_cnt <= '1';
      end if;
      if(start_cnt='1')then
        if(unsigned(cnt)<102129222)then -- reset signal should longer than 1 sample period??
          cnt <= std_logic_vector(unsigned(cnt)+1);
          reset <= '1';
        else
          start_cnt <= '0';
          reset <= '0';
          cnt <= (others=>'0');
        end if;
      end if; 
    end if;
  end if;
end process;


-- Port map UART interface component
-- One side of the interface connects to the UART cable
-- The other side connect to your FPGA logic (i.e. process_data component)
UART_1  : mmu_uart_top
port map
(
  Clk     => sysclk,          -- main clock (33 MHz)
  Reset_n => reset,           -- main reset(phjones made active high)
  TXD     => FPGA_SERIAL1_TX, -- RS232 TX data
  RXD     => FPGA_SERIAL1_RX, -- RS232 RX data
  --ck_div => x"0D90", --100 MHz, 9600
  ck_div => x"10F4", --125 MHz, 9600
  --ck_div  => x"0004", --for simulation
  --ck_div  => x"06C8", -- 50 MHz, 9600
                              -- clock divider value
                              -- used to get the baud rate
                              -- baud_rate = F(clk) / (ck_div * 3)
  -- bus interface

  CE_N    => '0',            -- chip enable
  WR_N    => WR_N,           -- write enable
  RD_N    => RD_N,           -- read enable
  A0      => '0',            -- 0 - Rx/TX data reg; 1 - status reg
  D_IN    => D_IN,           -- Data to send off-chip
  D_OUT   => D_OUT,          -- Data recieved to the chip 

  -- interrupt signals- same signals as the status register bits
  RX_full     => RX_full,  -- Recived byte availbe next clock cycle
  TX_busy_n   => TX_busy_n
);


-- Port map process_data for processing recived data
process_data_1  : process_data
port map
(
  clk       => sysclk,
  reset     => reset,
  data_in   => D_OUT,  -- Data recived by the FPGA
  RX_full   => RX_full, -- Indicate a byte has been recived by the UART
  TX_busy_n => TX_busy_n, -- Indicate UART is busy transmitting
  RD_n      => RD_n,   -- Request to read a byte from the UART
  WR_n      => WR_n,  -- Write a byte to the UART inteface for transmission
  data_out  => D_IN,  -- Data to be transmitted by the FPGA
  soft_reset => soft_reset,
--  pRBUS_DATA => pRBUS_DATA,
--  pRBUS_ADDR => pRBUS_ADDR,
--  pRBUS_EN => pRBUS_EN,
  pRBUS_DATA => "0000000000000000",
  pRBUS_ADDR => "00000000",
  pRBUS_EN => '1',
  LD0 => LD0,
  LD1 => LD1,
  LD2 => LD2
);


end rtl;
