-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
--                                                                           --
-- File Name: MP1_top_driver.vhd                                             --
-- Author: Phillip Jones (phjones@iastate.edu)                               --
-- Date: 8/27/2010                                                           --
--                                                                           --
-- Description: Drives to MP1_top for simulation                             --
--                                                                           --
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.STD_LOGIC_ARITH.ALL;
use IEEE.STD_LOGIC_UNSIGNED.ALL;
use work.uart_pkg.all;

entity MP1_top_driver is
port
(
  sysclk    : in  std_logic;  -- system clock
  RESET_low : in  std_logic;  -- Active low (polartity immediately change to active high)
  FPGA_SERIAL1_TX  : out std_logic;
  FPGA_SERIAL1_RX  : in  std_logic;
  Send_Data_array : in TEST_DATA_type;
  send_finish : out std_logic
);  
end MP1_top_driver;

architecture rtl of MP1_top_driver is

----------------------------------------------
--       Component declarations             --
----------------------------------------------

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
        RX_full     : out std_logic;
        TX_busy_n   : out std_logic

);
end component;


----------------------------------------------
--          type declarations             --
----------------------------------------------
  -- type to hold simulation data


----------------------------------------------
--          Signal declarations             --
----------------------------------------------
signal reset     : std_logic;  -- Reset active high
signal WR_N      : std_logic;  -- Active low write enable
signal RD_N      : std_logic;  -- Active low read enable
signal TXD_temp  : std_logic;  -- Allow output of TXD to test pin 

signal D_IN   : std_logic_vector(7 downto 0);  -- Data to Transmit
signal D_OUT  : std_logic_vector(7 downto 0);  -- Data Recieved
signal Data_RX_reg : std_logic_vector(7 downto 0);  -- Register RX Data

signal RX_full   : std_logic;     -- Byte of Data to Ready to read
signal TX_busy_n : std_logic;     -- Active low indicate busy transmitting
signal my_pulse  : std_logic;     -- Ensure WE_N on low for 1 clk

signal my_pause_cnt : std_logic_vector (19 downto 0); -- Slow down input ~5x


signal array_index : integer range 0 to data_size-1; -- Index into test
signal send_finish_sig : std_logic;
  
--signal Send_Data_array : TEST_DATA_type :=
--  (
--    x"00", x"01", x"02", x"03", x"04", x"05", x"06", x"07",
--    x"08", x"09", x"0a", x"0b", x"0c", x"0d", x"0e", x"0f",
--    x"10", x"11", x"12", x"13", x"14", x"15", x"16", x"17",
--    x"18", x"19", x"1a", x"1b", x"1c", x"1d", x"1e", x"1f",
--    x"20", x"21", x"22", x"23", x"24", x"25", x"26", x"27",
--    x"28", x"29", x"2a", x"2b", x"2c", x"2d", x"2e", x"2f",
--    x"30", x"31", x"32", x"33", x"34", x"35", x"36", x"37",
--    x"38", x"39", x"3a", x"3b", x"3c", x"3d", x"3e", x"3f",      
--    x"40", x"41", x"42", x"43", x"44", x"45", x"46", x"47",
--    x"48", x"49", x"4a", x"4b", x"4c", x"4d", x"4e", x"4f",
--    x"50", x"51", x"52", x"53", x"54", x"55", x"56", x"57",
--    x"58", x"59", x"5a", x"5b", x"5c", x"5d", x"5e", x"5f",
--    x"60", x"61", x"62", x"63", x"64", x"65", x"66", x"67",
--    x"68", x"69", x"6a", x"6b", x"6c", x"6d", x"6e", x"6f",
--    x"70", x"71", x"72", x"73", x"74", x"75", x"76", x"77",
--    x"78", x"79", x"7a", x"7b", x"7c", x"7d", x"7e", x"7f",
--    x"80", x"81", x"82", x"83", x"84", x"85", x"86", x"87",
--    x"88", x"89", x"8a", x"8b", x"8c", x"8d", x"8e", x"8f",
--    x"90", x"91", x"92", x"93", x"94", x"95", x"96", x"97",
--    x"98", x"99", x"9a", x"9b", x"9c", x"9d", x"9e", x"9f",
--    x"a0", x"a1", x"a2", x"a3", x"a4", x"a5", x"a6", x"a7",
--    x"a8", x"a9", x"aa", x"ab", x"ac", x"ad", x"ae", x"af",
--    x"b0", x"b1", x"b2", x"b3", x"b4", x"b5", x"b6", x"b7",
--    x"b8", x"b9", x"ba", x"bb", x"bc", x"bd", x"be", x"bf",      
--    x"c0", x"c1", x"c2", x"c3", x"c4", x"c5", x"c6", x"c7",
--    x"c8", x"c9", x"ca", x"cb", x"cc", x"cd", x"ce", x"cf",
--    x"d0", x"d1", x"d2", x"d3", x"d4", x"d5", x"d6", x"d7",
--    x"d8", x"d9", x"da", x"db", x"dc", x"dd", x"de", x"df",
--    x"e0", x"e1", x"e2", x"e3", x"e4", x"e5", x"e6", x"e7",
--    x"e8", x"e9", x"ea", x"eb", x"ec", x"ed", x"ee", x"ef",
--    x"f0", x"f1", x"f2", x"f3", x"f4", x"f5", x"f6", x"f7",
--    x"f8", x"f9", x"fa", x"fb", x"fc", x"fd", x"fe", x"ff"
--  );

begin


------------------------------------------------------------
------------------------------------------------------------
--                                                        --
-- Process Name: Send_chars                               --
--                                                        --
-- Send characters to MP1_top                             --
--                                                        --
------------------------------------------------------------
------------------------------------------------------------
Send_chars : process(sysclk)
begin
  if (sysclk = '1' and sysclk'event) then
    
    -- Defaults

    WR_N  <= '1';
    D_IN  <= D_IN;
    array_index <= array_index;
	 my_pulse <= '1'; -- Ensure WR_N on active for on clk
    
    if(reset = '1') then
      send_finish_sig <= '0';
      WR_N  <= '1';
      D_IN  <= (others => '0');
      array_index <= 0;
		my_pulse <= '1';
		my_pause_cnt <= (others => '0'); -- Slow down input by ~5x
    else
	 
	   my_pause_cnt <= my_pause_cnt + 1; -- Slow down input by ~5x
	 
	   if(TX_busy_n = '0') then
	     my_pulse <= '1';
	   end if;
		                                           -- Slow down input ~5x
      --if(TX_busy_n = '1' and my_pulse = '1' and my_pause_cnt = x"30D40") then
      --if(TX_busy_n = '1' and my_pulse = '1' and my_pause_cnt = x"02B40" and send_finish_sig = '0') then
      if(TX_busy_n = '1' and my_pulse = '1' and my_pause_cnt = x"2B40" and send_finish_sig = '0') then
  		  my_pause_cnt <= (others => '0');  -- Slow down input by ~5x
  		  my_pulse <= '0';
        WR_N     <= '0';   -- start transmission	  
        D_IN     <= Send_Data_array(array_index);
        array_index  <= array_index + 1;
        if(array_index=174)then--number of data
          send_finish_sig <= '1';
          WR_N     <= '1';
        end if;
      end if;

    end if;
      if(send_finish_sig='1')then
          WR_N     <= '1';  
        end if;
  end if;
end process Send_chars;

send_finish <= send_finish_sig;
------------------------------------------------------------
------------------------------------------------------------
--                                                        --
-- Process Name: Recv_chars                               --
--                                                        --
-- Send characters to MP1_top                             --
--                                                        --
------------------------------------------------------------
------------------------------------------------------------
Recv_chars : process(sysclk)
begin
  if (sysclk = '1' and sysclk'event) then
    -- Defaults
    RD_N         <= '1';
    Data_RX_reg  <= Data_RX_reg;

    if(reset = '1') then
      RD_N        <= '1';
      Data_RX_reg <= (others => '0');
    else
    
      -- Check if a byte has arrived
      if(RX_full = '1') then
        Data_RX_reg <= D_OUT;  -- Capture data from VHDL under test
        RD_N        <= '0';    -- clear read full flag
      end if;

    end if;
      
  end if;
end process Recv_chars;



-- Combinational assignments
FPGA_SERIAL1_TX  <= TXD_temp;
--reset <= not RESET_low;  -- change reset to active high
reset <= RESET_low; 


-- Port map UART
UART_1  : mmu_uart_top
port map
(
  Clk     => sysclk,          -- main clock (33 MHz)
  Reset_n => reset,           -- main reset(phjones made active high)
  TXD     => TXD_temp,        -- RS232 TX data
  RXD     => FPGA_SERIAL1_RX, -- RS232 RX data
  --clk_div => "0D90",
  ck_div  => x"0004",
  --ck_div  => x"0478",
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
  RX_full     => RX_full,
  TX_busy_n   => TX_busy_n
);


end rtl;
