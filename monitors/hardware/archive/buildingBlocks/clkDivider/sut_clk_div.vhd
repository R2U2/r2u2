-------------------------------------------------------------------------------
-- Project    : CevTes RVU (Runtime Verification Unit)
-------------------------------------------------------------------------------
-- File       : sut_clk_div.vhd
-- Author     : Thomas Reinbacher
-- Copyright  : 2011, Thomas Reinbacher (treinbacher@ecs.tuwien.ac.at)
--              Vienna University of Technology, ECS Group
-------------------------------------------------------------------------------
-- Description: A generic clock divider 
-------------------------------------------------------------------------------

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

entity sut_clk_div is

  generic (
    PRESCALER_WIDTH : integer);         -- the prescaler width

  port (
    clk            : in  std_logic;     -- input clock
    reset_n        : in  std_logic;     -- active-low reset
    en             : in  std_logic;     -- a general purpose enable signal
    clk_div        : out std_logic;  -- output clock (only active if enable is '1'
    clk_div_always : out std_logic;  -- output clock that counts even if the enable signal is not set
    prescaler      : in  std_logic_vector(PRESCALER_WIDTH downto 0)
    );

end sut_clk_div;

architecture rtl of sut_clk_div is

  signal s_clk_ctr        : std_logic_vector(PRESCALER_WIDTH downto 0);
  signal s_clk_div        : std_logic;
  signal s_clk_div_always : std_logic;
  signal s_clk_div_intern : std_logic;

begin  -- rtl

  clk_div        <= s_clk_div;
  clk_div_always <= s_clk_div_always;
  -- purpose: Clock divider process
  -- type   : sequential
  -- inputs : clk, reset_n
  -- outputs: clk_div, s_clk_ctr 
  p_clk_div : process (clk, reset_n)
  begin  -- process p_clk_div
    if reset_n = '0' then               -- asynchronous reset (active low)
      s_clk_ctr        <= (others => '0');
      s_clk_div_intern <= '0';
    elsif clk'event and clk = '1' then  -- rising clock edge
      s_clk_ctr <= s_clk_ctr +1;
      if(s_clk_ctr = prescaler)then
        s_clk_div_intern <= not s_clk_div_intern;
        s_clk_ctr        <= (others => '0');
      end if;

      s_clk_div_always <= s_clk_div_intern;

      if en = '1' then
        s_clk_div <= s_clk_div_intern;
      else
        s_clk_div <= '0';
      end if;
      
    end if;
  end process p_clk_div;

end rtl;


