-------------------------------------------------------------------------------
-- Project    : CevTes RVU (Runtime Verification Unit)
-------------------------------------------------------------------------------
-- File       : debounce_fsm.vhd
-- Author     : Thomas Polzer      
-- Copyright  : 2011, Thomas Reinbacher (treinbacher@ecs.tuwien.ac.at)
--              Vienna University of Technology, ECS Group
-------------------------------------------------------------------------------
-- Description: debouncer state machine                                        
------------------------------------------------------------------------------- 

library ieee;
use ieee.std_logic_1164.all;
use work.math_pkg.all;

----------------------------------------------------------------------------------
--                                 ENTITY                                       --
----------------------------------------------------------------------------------

-- debouncer for buttons - checks if an incoming signal is stable for a specified period of time 
entity debounce_fsm is
  generic
    (
      -- clock frequency [Hz]
      CLK_FREQ    : integer;
      -- debouce timeout
      TIMEOUT     : time range 100 us to 100 ms := 1 ms;
      -- reset value of the output signal
      RESET_VALUE : std_logic
      );
  port
    (
      clk   : in std_logic;
      res_n : in std_logic;

      i : in  std_logic;
      o : out std_logic;

      reinit       : in std_logic;
      reinit_value : in std_logic
      );
end entity debounce_fsm;

--- EOF  ---
