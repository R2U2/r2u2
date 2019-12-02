-------------------------------------------------------------------------------
-- Project    : CevTes RVU (Runtime Verification Unit)
-------------------------------------------------------------------------------
-- File       : fetch_stage.vhd
-- Author     : Andreas Hagmann (ahagmann@ecs.tuwien.ac.at)
-- Copyright  : 2012, Thomas Reinbacher (treinbacher@ecs.tuwien.ac.at)
--              Vienna University of Technology, ECS Group
-------------------------------------------------------------------------------
-- Description: fetch pipeline stage
-------------------------------------------------------------------------------
library ieee;
use ieee.std_logic_1164.all;
use work.mu_monitor_pkg.all;
use work.cevLib_unsigned_pkg.all;

entity fetch_stage is
  port (
    clk     : in  std_logic;
    reset_n : in  std_logic;
    i       : in  fetch_in_t;
    o       : out fetch_out_t
    );
end entity;

architecture arch of fetch_stage is
  type state_t is (IDLE, STALL, FETCH);

  type reg_t is record
    state           : state_t;
    reg             : fetch_register_t;
    program_counter : program_counter_t;
  end record;
  
  constant REGISTER_RESET : reg_t := (
    IDLE,
    FETCH_REGISTER_T_NULL,
    PROGRAMM_COUNTER_DEFAULT--(others => '0')
    );

  signal this, this_nxt : reg_t;
begin

  comb : process(this, i)
    variable nxt    : reg_t;
    variable finish : std_logic;
  begin
    nxt    := this;
    -- defaults
    finish := '0';

    case (this.state) is
      when IDLE =>
        if i.start = '1' then
          nxt.state := FETCH;
        end if;
        
      when STALL =>
        finish := '1';

      when FETCH =>
        nxt.reg.command         := slv_to_instruction(i.memData);
        nxt.reg.program_counter := this.program_counter;
        nxt.program_counter     := this.program_counter + 1;
        finish                  := '1';
        
    end case;

    if finish = '1' then
      nxt.state := STALL;

      if i.nxt_ack = '1' then
        if nxt.reg.command.command = OP_END_SEQUENCE then
          nxt.state           := IDLE;
          nxt.program_counter := (others => '0');
        else
          nxt.state := FETCH;
        end if;
      end if;
    end if;

    o.memAddr <= nxt.program_counter;
    o.fin     <= finish;
    o.reg     <= this.reg;
    this_nxt  <= nxt;
  end process;

  reg : process(clk, reset_n)
  begin
    if reset_n = '0' then
      this <= REGISTER_RESET;
    elsif rising_edge(clk) then
      this <= this_nxt;
    end if;
  end process;

end architecture;

