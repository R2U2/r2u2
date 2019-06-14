-------------------------------------------------------------------------------
-- Project    : CevTes RVU (Runtime Verification Unit)
-------------------------------------------------------------------------------
-- File       : debounce_fsm_beh.vhd
-- Author     : Thomas Polzer      
-- Copyright  : 2011, Thomas Reinbacher (treinbacher@ecs.tuwien.ac.at)
--              Vienna University of Technology, ECS Group
-------------------------------------------------------------------------------
-- Description: debouncer_fsm_beh                                        
------------------------------------------------------------------------------- 

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

architecture beh of debounce_fsm is
  -- clock frequency [Hz]
  constant CLK_PERIOD : time    := 1E9 / CLK_FREQ * 1 ns;
  -- debouce timeout
  constant CNT_MAX    : integer := TIMEOUT / CLK_PERIOD;
  type     DEBOUNCE_FSM_STATE_TYPE is
    (REINIT0, REINIT1, IDLE0, TIMEOUT0, IDLE1, TIMEOUT1);
  signal debounce_fsm_state, debounce_fsm_state_next : DEBOUNCE_FSM_STATE_TYPE;
  signal cnt, cnt_next                               : integer range 0 to CNT_MAX;
begin

  next_state : process(debounce_fsm_state, i, reinit, reinit_value, cnt)
  begin
    -- default
    debounce_fsm_state_next <= debounce_fsm_state;

    case debounce_fsm_state is
      -- reinit state for '0'
      when REINIT0 =>
        debounce_fsm_state_next <= TIMEOUT0;
        -- reinit state for '1'
      when REINIT1 =>
        debounce_fsm_state_next <= TIMEOUT1;
        -- idle status - waiting for i to become '1'
      when IDLE0 =>
        if reinit = '1' and reinit_value = '0' then
          debounce_fsm_state_next <= REINIT0;
        elsif reinit = '1' and reinit_value = '1' then
          debounce_fsm_state_next <= REINIT1;
          -- next state will check duration of high level
        elsif i = '1' then
          debounce_fsm_state_next <= TIMEOUT0;
        end if;
        -- check if i = '1' for the period of TIMEOUT
      when TIMEOUT0 =>
        if reinit = '1' and reinit_value = '0' then
          debounce_fsm_state_next <= REINIT0;
        elsif reinit = '1' and reinit_value = '1' then
          debounce_fsm_state_next <= REINIT1;
          -- glitch, no button pressed
        elsif i = '0' then
          debounce_fsm_state_next <= IDLE0;
          -- button has been pressed
        elsif cnt = CNT_MAX - 1 then
          debounce_fsm_state_next <= IDLE1;
        end if;
        -- idle status - waiting for i to become '0'
      when IDLE1 =>
        if reinit = '1' and reinit_value = '0' then
          debounce_fsm_state_next <= REINIT0;
        elsif reinit = '1' and reinit_value = '1' then
          debounce_fsm_state_next <= REINIT1;
          -- next state will check duration of low level
        elsif i = '0' then
          debounce_fsm_state_next <= TIMEOUT1;
        end if;
        -- check if i = '0' for the period of TIMEOUT
      when TIMEOUT1 =>
        if reinit = '1' and reinit_value = '0' then
          debounce_fsm_state_next <= REINIT0;
        elsif reinit = '1' and reinit_value = '1' then
          debounce_fsm_state_next <= REINIT1;
          -- glitch, no button pressed  
        elsif i = '1' then
          debounce_fsm_state_next <= IDLE1;
          -- button has been pressed
        elsif cnt = CNT_MAX - 1 then
          debounce_fsm_state_next <= IDLE0;
        end if;
    end case;
  end process next_state;

  --------------------------------------------------------------------
  --                    PROCESS : OUTPUT                            --
  -------------------------------------------------------------------- 

  output : process(debounce_fsm_state, cnt)
  begin
    o        <= RESET_VALUE;
    cnt_next <= 0;                      -- error fixed
    case debounce_fsm_state is
      when REINIT0 =>
        o <= '0';
      when REINIT1 =>
        o <= '1';
        -- idle state is '0'
      when IDLE0 =>
        o <= '0';
        -- check duration of hight level
      when TIMEOUT0 =>
        o        <= '0';
        cnt_next <= cnt + 1;
        -- idle state is '1'
      when IDLE1 =>
        o <= '1';
        -- check duration of low level
      when TIMEOUT1 =>
        o        <= '1';
        cnt_next <= cnt + 1;
    end case;
    
  end process output;

  assert RESET_VALUE = '0' or RESET_VALUE = '1' report
    "RESET_VALUE may only be 0 or 1!" severity failure;

  --------------------------------------------------------------------
  --                    PROCESS : SYNC                              --
  --------------------------------------------------------------------  

  sync : process(clk, res_n)
  begin
    if res_n = '0' then
      if RESET_VALUE = '0' then
        debounce_fsm_state <= IDLE0;
      else
        debounce_fsm_state <= IDLE1;
      end if;
      cnt <= 0;
    elsif rising_edge(clk) then
      debounce_fsm_state <= debounce_fsm_state_next;
      cnt                <= cnt_next;
    end if;
  end process sync;
end architecture beh;
