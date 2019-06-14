-------------------------------------------------------------------------------
-- Project    : CevTes RVU (Runtime Verification Unit)
-------------------------------------------------------------------------------
-- File       : timer_pkg.vhd
-- Author     : Johannes Geist           johannes.geist@technikum-wien.at
-- Copyright  : 2011, Thomas Reinbacher (treinbacher@ecs.tuwien.ac.at)
--              Vienna University of Technology, ECS Group
-------------------------------------------------------------------------------
-- Description: Package for timer-constants and components.  
-------------------------------------------------------------------------------
library ieee;
use ieee.std_logic_1164.all;
package timer_pkg is

  -----------------------------------------------------------------------------
  --                                 CONSTANTS                               --
  -----------------------------------------------------------------------------
  constant CONST_100MHZ : integer := 100;
  constant CONST_128MHZ : integer := 128;  -- 128 mhz
  constant CONST_160MHZ : integer := 160;  -- 160 mhz
  constant CONST_1US    : integer := 1;   -- multiplikation for us time base
  constant CONST_10US   : integer := 10;  -- multiplikation for 10 us time base
  constant CONST_100US  : integer := 100;  -- multiplikation for 100 us time base
  constant CONST_1MS    : integer := 1000;  -- multiplikation for 1ms tiem base
  constant CONST_10MS   : integer := 10000;  -- multiplikation for 10ms tiem base
  constant CONST_100MS  : integer := 100000;  -- multiplikation for 100ms time base
  constant CONST_1S     : integer := 1000000;  -- multiplikation for 1s tiem base

  -----------------------------------------------------------------------------
  --                            COMPONENT                                    --
  -----------------------------------------------------------------------------

  -- comments in timer_fsm.vhd



  component timer_fsm
    generic (
      TIMER_WIDTH : integer;
      TICK        : integer);
    port (
      clk       : in  std_logic;
      reset_n   : in  std_logic;
      go        : in  std_logic;
      stop      : in  std_logic;
      expired   : out std_logic;
      period    : in  std_logic_vector((TIMER_WIDTH - 1) downto 0);
      remaining : out std_logic_vector((TIMER_WIDTH - 1) downto 0));
  end component;

end timer_pkg;
