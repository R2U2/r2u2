-------------------------------------------------------------------------------
-- Project    : CevTes RVU (Runtime Verification Unit)
-------------------------------------------------------------------------------
-- File       : sut_clk_div_pkg.vhd
-- Author     : Thomas Reinbacher
-- Copyright  : 2012, Thomas Reinbacher (treinbacher@ecs.tuwien.ac.at)
--              Vienna University of Technology, ECS Group
-------------------------------------------------------------------------------
-- Description: sut_clk_div package 
-------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;

package sut_clk_div_pkg is

   component sut_clk_div
    generic (
      PRESCALER_WIDTH : integer);
    port (
      clk            : in  std_logic;
      reset_n        : in  std_logic;
      en             : in  std_logic;
      clk_div        : out std_logic;
      clk_div_always : out std_logic;
      prescaler      : in  std_logic_vector(PRESCALER_WIDTH downto 0));
  end component;   

end package sut_clk_div_pkg;


