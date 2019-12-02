------------------------------------------------------------------------------
-- Project    : CevTes RVU (Runtime Verification Unit)
-------------------------------------------------------------------------------
-- File       : write_back.vhd
-- Author     : Andreas Hagmann (ahagmann@ecs.tuwien.ac.at)
-- Copyright  : 2012, Thomas Reinbacher (treinbacher@ecs.tuwien.ac.at)
--              Vienna University of Technology, ECS Group
-------------------------------------------------------------------------------
-- Description: write back pipeline stage
-------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use work.math_pkg.all;
use work.cevLib_unsigned_pkg.all;
use work.mu_monitor_pkg.all;

entity write_back_stage is
  port (
    clk     : in  std_logic;
    reset_n : in  std_logic;
    i       : in  write_back_in_t;
    o       : out write_back_out_t
    );
end entity;

architecture arch of write_back_stage is
  type state_t is (IDLE, WRITE);

  type reg_t is record
    state : state_t;
  end record;
  
  constant REGISTER_RESET : reg_t := (
    state => IDLE
    );

  signal this, this_nxt : reg_t;
begin

  comb : process(this, i)
    variable nxt : reg_t;
  begin
    nxt               := this;
    -- defaults
    o.ack             <= '0';
    o.nowMemory.write <= '0';

    if i.prev_fin = '1' then
      nxt.state := WRITE;
      o.ack     <= '1';
    else
      nxt.state := IDLE;
    end if;

    case (this.state) is
      when IDLE =>
        null;
        
      when WRITE =>
        o.nowMemory.write <= '1';
        
    end case;

    o.nowMemory.rdAddrA <= (others => '0');
	 o.nowMemory.rdAddrB <= (others => '0');
	 o.nowMemory.rdAddrC <= (others => '0');
    o.nowMemory.wrData  <= i.reg.result;
    o.nowMemory.wrAddr  <= i.reg.program_counter;
    this_nxt            <= nxt;
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

