-------------------------------------------------------------------------------
-- Project    : CevTes RVU (Runtime Verification Unit)
-------------------------------------------------------------------------------
-- File       : rtc.vhd
-- Author     : Patrick Moosbrugger (p.moosbrugger@gmail.com)
-- Copyright  : 2011, Thomas Reinbacher (treinbacher@ecs.tuwien.ac.at)
--              Vienna University of Technology, ECS Group
-------------------------------------------------------------------------------
-- Description: A simple generic rtc with enable signal and overflow detection
--              The countervalue is not loadable, it starts from 0 after reset 
-------------------------------------------------------------------------------
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use ieee.std_logic_unsigned.all;

entity rtc is
  
  generic (
    RTC_WIDTH : integer
    );                                  -- Clock cycle ticks for one period

  port (
    clk      : in  std_logic;           -- clock
    reset_n  : in  std_logic;           -- active low reset
    en       : in  std_logic;           -- Enable sigal
    overflow : out std_logic;           -- Overflow detected
    cntvalue : out std_logic_vector((RTC_WIDTH - 1) downto 0)  -- rtc value
    );
end rtc;

architecture rtl of rtc is

  signal s_cntvalue : std_logic_vector((RTC_WIDTH - 1) downto 0);

begin

  count : process (clk, reset_n)
  begin
    if reset_n = '0' then               -- asynchronous reset
      s_cntvalue <= (others => '0');
      overflow   <= '0';
    elsif clk'event and clk = '1' then  -- rising clock edge
      if en = '1' then
        s_cntvalue <= s_cntvalue + '1';
        --check if rtc value has reached top
        if s_cntvalue = (s_cntvalue'range => '1') then
          overflow <= '1';
        end if;

      end if;
    end if;
  end process count;

  cntvalue <= s_cntvalue;

end rtl;
