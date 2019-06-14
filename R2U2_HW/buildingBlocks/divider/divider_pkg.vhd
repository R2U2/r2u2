-------------------------------------------------------------------------------
-- Project    : CevTes RVU (Runtime Verification Unit)
-------------------------------------------------------------------------------
-- File       : divider_pkg.vhd
-- Author     : Thomas Reinbacher      
-- Copyright  : 2012, Thomas Reinbacher (treinbacher@ecs.tuwien.ac.at)
--              Vienna University of Technology, ECS Group
-------------------------------------------------------------------------------
-- Description: divider_pkg                                        
------------------------------------------------------------------------------- 

library ieee;
use ieee.std_logic_1164.all;

package divider_pkg is

  component divider_fsm
    generic (
      NUM_OF_BITS : integer);
    port (
      clk       : in  std_logic;
      reset_n   : in  std_logic;
      enable    : in  std_logic;
      run       : in  std_logic;
      dividend  : in  std_logic_vector((NUM_OF_BITS - 1) downto 0);
      divisor   : in  std_logic_vector((NUM_OF_BITS - 1) downto 0);
      quotient  : out std_logic_vector((NUM_OF_BITS - 1) downto 0);
      remainder : out std_logic_vector((NUM_OF_BITS - 1) downto 0);
      busy      : out std_logic;
      fin       : out std_logic);
  end component;

end divider_pkg;
