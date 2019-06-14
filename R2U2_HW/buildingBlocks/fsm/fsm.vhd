-------------------------------------------------------------------------------
-- Project    : CevTes RVU (Runtime Verification Unit)
-------------------------------------------------------------------------------
-- File       : fsm.vhd
-- Author     : Thomas Reinbacher
-- Copyright  : 2011, Thomas Reinbacher (treinbacher@ecs.tuwien.ac.at)
--              Vienna University of Technology, ECS Group
-------------------------------------------------------------------------------
-- Description: A finite state machine template 
-------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity fsm is
  
  port (
    clk     : in  std_logic;
    reset_n : in  std_logic;
    eventA  : in  std_logic;
    eventB  : in  std_logic;
    eventC  : in  std_logic;
    o       : out std_logic);
end fsm;

architecture rtl of fsm is

  type   FSM_STATE_TYPE is (IDLE, DO_FIRST, DO_SND, DO_THIRD);
  signal fsm_state      : FSM_STATE_TYPE;
  signal fsm_state_next : FSM_STATE_TYPE;
  -- declare other signals here!

begin
  next_state_logic : process (fsm_state, eventA, eventB, eventC)
  begin  -- process next_state_logic
    --default
    fsm_state_next <= fsm_state;

    case fsm_state is
      when IDLE =>
        fsm_state_next <= DO_FIRST;
      when DO_FIRST =>
        if eventA = '1' and eventB = '0' then
          fsm_state_next <= DO_SND;
        elsif eventA = '1' and eventB = '1' then
          fsm_state_next <= DO_THIRD;
        end if;
        fsm_state_next <= DO_SND;
      when DO_SND =>
        if eventB = '1' then
          fsm_state_next <= DO_THIRD;
        else
          fsm_state_next <= IDLE;
        end if;
      when DO_THIRD =>
        fsm_state_next <= DO_FIRST;
      when others => null;
    end case;
  end process next_state_logic;

  output : process (fsm_state)
  begin  -- process output
    o <= '0';
    case fsm_state is
      when IDLE =>
        o <= '0';
      when DO_FIRST =>
        o <= '1';
      when DO_SND =>
        o <= '0';
      when DO_THIRD =>
        o <= '1';
      when others => null;
    end case;
  end process output;

  sync : process (clk, reset_n)
  begin  -- process sync
    if reset_n = '0' then               -- asynchronous reset (active low)
      fsm_state <= IDLE;
    elsif clk'event and clk = '1' then  -- rising clock edge
      fsm_state <= fsm_state_next;
    end if;
  end process sync;
end rtl;
