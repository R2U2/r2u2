-------------------------------------------------------------------------------
-- Project    : CevTes RVU (Runtime Verification Unit)
-------------------------------------------------------------------------------
-- File       : debounce.vhd
-- Author     : Thomas Polzer      
-- Copyright  : 2011, Thomas Reinbacher (treinbacher@ecs.tuwien.ac.at)
--              Vienna University of Technology, ECS Group
-------------------------------------------------------------------------------
-- Description: debouncer                                        
------------------------------------------------------------------------------- 

library ieee;
use ieee.std_logic_1164.all;

-- connects a debouncer with a synchronizer
entity debounce is
  generic
    (
      -- clock frequency [Hz]
      CLK_FREQ    : integer;
      -- debouce timeout
      TIMEOUT     : time range 100 us to 100 ms := 1 ms;
      -- reset value of the output signal
      RESET_VALUE : std_logic                   := '0';
      -- number of stages in the input synchronizer
      SYNC_STAGES : integer range 2 to integer'high
      );
  port
    (
      clk   : in std_logic;
      res_n : in std_logic;

      data_in  : in  std_logic;
      data_out : out std_logic;

      reinit       : in std_logic;
      reinit_value : in std_logic
      );
end entity debounce;

--- EOF  ---
