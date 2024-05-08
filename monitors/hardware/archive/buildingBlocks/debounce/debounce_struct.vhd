-------------------------------------------------------------------------------
-- Project    : CevTes RVU (Runtime Verification Unit)
-------------------------------------------------------------------------------
-- File       : debounce_struct.vhd
-- Author     : Thomas Polzer      
-- Copyright  : 2011, Thomas Reinbacher (treinbacher@ecs.tuwien.ac.at)
--              Vienna University of Technology, ECS Group
-------------------------------------------------------------------------------
-- Description: debouncer                                        
------------------------------------------------------------------------------- 

library ieee;
use ieee.std_logic_1164.all;
use work.sync_pkg.all;
use work.debounce_pkg.all;
use work.math_pkg.all;

architecture struct of debounce is
  signal data_sync : std_logic;
begin

  -- synchronizer
  sync_inst : sync
    generic map
    (
      SYNC_STAGES => SYNC_STAGES,
      RESET_VALUE => RESET_VALUE
      )
    port map
    (
      clk      => clk,
      res_n    => res_n,
      data_in  => data_in,
      data_out => data_sync
      );

  -- debouncer state machine
  fsm_inst : debounce_fsm
    generic map
    (
      CLK_FREQ    => CLK_FREQ,
      TIMEOUT     => TIMEOUT,
      RESET_VALUE => RESET_VALUE
      )
    port map
    (
      clk          => clk,
      res_n        => res_n,
      i            => data_sync,
      o            => data_out,
      reinit       => reinit,
      reinit_value => reinit_value
      );

end architecture struct;
