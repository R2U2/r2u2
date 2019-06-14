------------------------------------------------------------------------------
-- Project    : CevTes RVU (Runtime Verification Unit)
-------------------------------------------------------------------------------
-- File       : load_stage.vhd
-- Author     : Andreas Hagmann (ahagmann@ecs.tuwien.ac.at)
-- Copyright  : 2012, Thomas Reinbacher (treinbacher@ecs.tuwien.ac.at)
--              Vienna University of Technology, ECS Group
-------------------------------------------------------------------------------
-- Description: load pipeline stage
-------------------------------------------------------------------------------
library ieee;
use ieee.std_logic_1164.all;
use work.mu_monitor_pkg.all;
use work.cevLib_unsigned_pkg.all;
use work.math_pkg.all;
use work.log_input_pkg.all;

entity load_stage is
  port (
    clk     : in  std_logic;
    reset_n : in  std_logic;
    i       : in  load_in_t;
    o       : out load_out_t
    );
end entity;

architecture arch of load_stage is
  type state_t is (IDLE, STALL, LOAD);
  type op_output_t is (MEM, REG);
  type interval_output_t is (MEM, REG);

  type reg_t is record
    state           : state_t;
    reg             : load_register_t;
    command         : instruction_t;
    op1_output      : op_output_t;
    op2_output      : op_output_t;
    interval_output : interval_output_t;
  end record;

  constant REGISTER_RESET : reg_t := (
    IDLE,
    LOAD_REGISTER_T_NULL,
    INSTRUCTION_T_NULL,
    MEM,
    MEM,
    MEM
    );

  signal this, this_nxt : reg_t;
begin

  comb : process(this, i)
    variable nxt     : reg_t;
    variable finish  : std_logic;
    variable op1Type : std_logic_vector(2-1 downto 0);
    variable op2Type : std_logic_vector(2-1 downto 0);
  begin
    nxt := this;

    -- defaults
    o.ack               <= '0';
    finish              := '0';
    op1Type             := i.reg.command.op1.is_memory_addr & i.reg.command.op1.is_immediate;
    op2Type             := i.reg.command.op2.is_memory_addr & i.reg.command.op2.is_immediate;
    o.nowMemory.rdAddrA <= i.reg.command.op1.value(log2c(ROM_LEN)-1 downto 0);
    o.nowMemory.rdAddrB <= i.reg.command.op2.value(log2c(ROM_LEN)-1 downto 0);
    o.nowMemory.rdAddrC <= i.reg.program_counter;
    o.preMemory.rdAddrA <= i.reg.command.op1.value(log2c(ROM_LEN)-1 downto 0);
    o.preMemory.rdAddrB <= i.reg.command.op2.value(log2c(ROM_LEN)-1 downto 0);
    o.preMemory.rdAddrC <= i.reg.program_counter;
    o.nowMemory.wrAddr  <= (others => '0');
    o.preMemory.wrAddr  <= (others => '0');
    o.nowMemory.write   <= '0';
    o.preMemory.write   <= '0';
    o.nowMemory.wrData  <= '0';
    o.preMemory.wrData  <= '0';
    nxt.op1_output      := REG;
    nxt.op2_output      := REG;
    nxt.interval_output := REG;
    o.buffer_nr         <= this.command.memoryAddr(log2c(DOT_BUFFER_LEN)-1 downto 0);

    -- after a read cycle forward data from memory direct to the output port
    o.reg <= this.reg;
    case this.op1_output is
      when MEM =>
        nxt.reg.operand.op1Now := i.nowMemory.rdDataA;
        nxt.reg.operand.op1Pre := i.preMemory.rdDataA;

        o.reg.operand.op1Now <= i.nowMemory.rdDataA;
        o.reg.operand.op1Pre <= i.preMemory.rdDataA;
      when REG =>
        null;
    end case;

    case this.op2_output is
      when MEM =>
        nxt.reg.operand.op2Now := i.nowMemory.rdDataB;
        nxt.reg.operand.op2Pre := i.preMemory.rdDataB;

        o.reg.operand.op2Now <= i.nowMemory.rdDataB;
        o.reg.operand.op2Pre <= i.preMemory.rdDataB;
      when REG =>
        null;
    end case;

    case this.interval_output is
      when MEM =>
        nxt.reg.operand.pre  := i.preMemory.rdDataC;
        nxt.reg.interval.min := i.interval_memory_data(2*TIMESTAMP_WIDTH-1 downto TIMESTAMP_WIDTH);
        nxt.reg.interval.max := i.interval_memory_data(TIMESTAMP_WIDTH-1 downto 0);

        o.reg.operand.pre  <= i.preMemory.rdDataC;
        o.reg.interval.min <= i.interval_memory_data(2*TIMESTAMP_WIDTH-1 downto TIMESTAMP_WIDTH);
        o.reg.interval.max <= i.interval_memory_data(TIMESTAMP_WIDTH-1 downto 0);
      when REG =>
        null;
    end case;

    case (this.state) is
      when IDLE =>
        if i.prev_fin = '1' then
          nxt.state := LOAD;
          o.ack     <= '1';
        end if;

      when STALL =>
        finish := '1';

      when LOAD =>
        nxt.command             := i.reg.command;
        nxt.reg.command         := i.reg.command.command;
        nxt.reg.program_counter := i.reg.program_counter;
        nxt.interval_output     := MEM;
        finish                  := '1';
        o.buffer_nr             <= i.reg.command.memoryAddr(log2c(DOT_BUFFER_LEN)-1 downto 0);
        nxt.reg.operand.fwd1    := '0';
        nxt.reg.operand.fwd2    := '0';
        nxt.reg.memoryAddr      := i.reg.command.memoryAddr;

        case op1Type is
          when "10" | "11" =>           -- from memory
            nxt.op1_output := MEM;
            -- forward path
            if i.reg.program_counter - 1 = i.reg.command.op1.value then  -- check: precalculate in fetch
              nxt.reg.operand.fwd1 := '1';
            end if;
          when "01" =>                  -- immediate
            nxt.reg.operand.op1Pre := i.reg.command.op1.value(0);
            nxt.reg.operand.op1Now := i.reg.command.op1.value(0);
          when "00" =>                  -- atomic
            nxt.reg.operand.op1Pre := i.last_atomics(conv_to_integer(i.reg.command.op1.value(log2c(ATOMICS_WIDTH)-1 downto 0)));
            nxt.reg.operand.op1Now := i.atomics(conv_to_integer(i.reg.command.op1.value(log2c(ATOMICS_WIDTH)-1 downto 0)));
          when others =>
            null;
        end case;

        case op2Type is
          when "10" | "11" =>           -- from memory
            nxt.op2_output := MEM;
            -- forward path
            if i.reg.program_counter - 1 = i.reg.command.op2.value then  -- check: precalculate in fetch
              nxt.reg.operand.fwd2 := '1';
            end if;
          when "01" =>                  -- immediate
            nxt.reg.operand.op2Pre := i.reg.command.op2.value(0);
            nxt.reg.operand.op2Now := i.reg.command.op2.value(0);
          when "00" =>                  -- atomic
            nxt.reg.operand.op2Pre := i.last_atomics(conv_to_integer(i.reg.command.op2.value(log2c(ATOMICS_WIDTH)-1 downto 0)));
            nxt.reg.operand.op2Now := i.atomics(conv_to_integer(i.reg.command.op2.value(log2c(ATOMICS_WIDTH)-1 downto 0)));
          when others =>
            null;
        end case;

    end case;

    if finish = '1' then
      nxt.state := STALL;

      if i.nxt_ack = '1' then
        if i.prev_fin = '1' then
          nxt.state := LOAD;
          o.ack     <= '1';
        else
          nxt.state := IDLE;
        end if;
      end if;
    end if;

    o.interval_memory_addr <= i.reg.command.intervalAddr(log2c(INTERVAL_MEMORY_LEN)-1 downto 0);
    o.fin                  <= finish;
    this_nxt               <= nxt;
  end process;

  reg_p : process(clk, reset_n)
  begin
    if reset_n = '0' then
      this <= REGISTER_RESET;
    elsif rising_edge(clk) then
      this <= this_nxt;
    end if;
  end process;

end architecture;
