-------------------------------------------------------------------------------
-- Project    : CevTes RVU (Runtime Verification Unit)
-------------------------------------------------------------------------------
-- File       : calc_stage.vhd
-- Author     : Daniel Schachinger
--              Patrick Moosbrugger (p.moosbrugger@gmail.com)
--              Andreas Hagmann (ahagmann@ecs.tuwien.ac.at)
-- Copyright  : 2012, Thomas Reinbacher (treinbacher@ecs.tuwien.ac.at)
--              Vienna University of Technology, ECS Group
-------------------------------------------------------------------------------
-- Description: calc pipeline stage
-------------------------------------------------------------------------------
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.mu_monitor_pkg.all;
use work.math_pkg.all;
use work.cevLib_unsigned_pkg.all;

entity calc_stage is
  port (
    clk     : in  std_logic;
    reset_n : in  std_logic;
    i       : in  calc_in_t;
    o       : out calc_out_t
    );
end entity;

architecture arch of calc_stage is
  type state_t is (IDLE, STALL, CALC, UPDATE_LIST, CALC_MTL, GARBAGE);
--  type select_time_t is (S_NONE, S_TIME, S_TIME_1);

  type reg_t is record
    state            : state_t;
    reg              : calc_register_t;
    initialized      : std_logic;
    operand          : operands_t;
    interval         : interval_t;
    memoryAddr       : std_logic_vector(7-1 downto 0);
    time_intervalMin : std_logic_vector(TIMESTAMP_WIDTH - 1 downto 0);
    time_intervalMax : std_logic_vector(TIMESTAMP_WIDTH - 1 downto 0);
    time_1           : std_logic_vector(TIMESTAMP_WIDTH - 1 downto 0);
    command          : operator_t;
    timestamp_buffer : timestamp_t;
    startup_cnt      : std_logic_vector(2*TIMESTAMP_WIDTH-1 downto 0);
    violated         : std_logic;
    violated_valid   : std_logic;
  end record;

  constant REGISTER_RESET : reg_t := (
    IDLE,
    CALC_REGISTER_T_NULL,
    '0',
    OPERANDS_T_NULL,
    INTERVAL_T_NULL,
    (others => '0'),
    (others => '0'),
    (others => '0'),
    (others => '0'),
    OP_NOP,
    TIMESTAMP_T_NULL,
    (others => '0'),
    '0',
    '0'
    );

  signal this, this_nxt : reg_t;
begin

  comb : process(this, i)
    variable nxt                : reg_t;
    variable finish             : std_logic;
    variable first_conjunct     : std_logic;
    variable second_conjunct    : std_logic;
    variable op1_falling_edge_r : std_logic;  -- todo: store edge in register
    variable op1RisingEdge_r    : std_logic;
    variable op2RisingEdge_r    : std_logic;
    variable op2_falling_edge_r : std_logic;
    variable feasible           : std_logic;
    --   variable select_time        : select_time_t;
  begin
    nxt := this;

    -- defaults
    o.ack  <= '0';
    finish := '0';
    o.idle <= '0';

    o.boxMemory.write           <= '0';
    o.violated                  <= this.violated;
    o.violated_valid            <= this.violated_valid;
    o.dotMemory.delete          <= '0';
    o.dotMemory.timestamp       <= (others => '0');
    o.dotMemory.fetch_buffer_nr <= (others => '0');
    o.dotMemory.sel             <= '0';
    o.dotMemory.add_start       <= '0';
    o.dotMemory.add_end         <= '0';
    o.dotMemory.set_tail        <= '0';
    o.dotMemory.reset_tail      <= '0';
    o.dotMemory.drop_tail       <= '0';
    o.dotMemory.delete          <= '0';
    o.boxMemory.rdAddr          <= this.memoryAddr(log2c(BOX_MEMORY_LEN)-1 downto 0);
    o.dotMemory.buffer_nr       <= this.memoryAddr(log2c(DOT_BUFFER_LEN)-1 downto 0);
    --  select_time            := S_NONE;

    o.calc_finish <= '0';

    -- detect edges
    if (this.operand.op1Pre = '0') and (this.operand.op1Now = '1') then
      op1RisingEdge_r := '1';
    else
      op1RisingEdge_r := '0';
    end if;

    if (this.operand.op1Pre = '1') and (this.operand.op1Now = '0') then
      op1_falling_edge_r := '1';
    else
      op1_falling_edge_r := '0';
    end if;

    if (this.operand.op2Pre = '0') and (this.operand.op2Now = '1') then
      op2RisingEdge_r := '1';
    else
      op2RisingEdge_r := '0';
    end if;

    if (this.operand.op2Pre = '1') and (this.operand.op2Now = '0') then
      op2_falling_edge_r := '1';
    else
      op2_falling_edge_r := '0';
    end if;

    if this.time_1 - i.dotMemory.tail.start.time >= this.interval.max - this.interval.min then  --this.intervalLength then   -- check: do not always calculate this
      feasible := '1';
    else
      feasible := '0';
    end if;

    case (this.state) is
      when IDLE =>
        o.idle <= '1';
        if i.prev_fin = '1' then
          nxt.state := CALC;
          o.ack     <= '1';
        end if;

      when CALC =>
        -- precalculations
        nxt.time_intervalMax    := i.time - i.reg.interval.max;
        nxt.time_intervalMin    := i.time - i.reg.interval.min;
        nxt.time_1              := i.time - 1;
        nxt.operand             := i.reg.operand;
        nxt.reg.program_counter := i.reg.program_counter;
        nxt.command             := i.reg.command;
        nxt.interval            := i.reg.interval;
        nxt.memoryAddr          := i.reg.memoryAddr;
        o.boxMemory.rdAddr      <= i.reg.memoryAddr(log2c(BOX_MEMORY_LEN)-1 downto 0);
        o.dotMemory.buffer_nr   <= i.reg.memoryAddr(log2c(DOT_BUFFER_LEN)-1 downto 0);

        if nxt.operand.fwd1 = '1' then
          nxt.operand.op1Now := this.reg.result;
        end if;

        if nxt.operand.fwd2 = '1' then
          nxt.operand.op2Now := this.reg.result;
        end if;

        -- switch to invert input signal
        case nxt.command is
          when OP_MTL_DIAMONDDIAMOND |
            OP_MTL_DIAMONDDOT =>
            nxt.operand.op1Pre := not nxt.operand.op1Pre;
            nxt.operand.op1Now := not nxt.operand.op1Now;
          when others =>
            null;
        end case;

        finish := '1';

--        if this.initialized = '0' then
--          case i.reg.command is
--            when OP_FALSE |
--              OP_MTL_BOXBOX | 
--              OP_MTL_BOXDOT |
--              OP_MTL_DIAMONDDOT |
--            OP_MTL_DIAMONDDIAMOND =>
--              nxt.operand.now := '0';
--            when OP_START |
--              OP_END =>
--              nxt.operand.now := nxt.operand.op1Now;
--            when OP_TRUE  =>
--              nxt.operand.now := '1';
--            when OP_ATOMIC =>
--              nxt.operand.now := '0';  -- this creates a rising edge on signals that are high at startup
--            when OP_NOT =>
--              nxt.operand.now := not nxt.operand.op1Now;
--            when OP_AND =>
--              nxt.operand.now := nxt.operand.op1Now and nxt.operand.op2Now;
--            when OP_OR =>
--              nxt.operand.now := nxt.operand.op1Now or nxt.operand.op2Now;
--            when OP_IMPLICIT =>
--              nxt.operand.now := (not nxt.operand.op1Now) or nxt.operand.op2Now;
--            when OP_EQUIVALENT =>
--              nxt.operand.now := nxt.operand.op1Now xnor nxt.operand.op2Now;
        --           when OP_PREVIOUSLY |
        --             OP_EVENTUALLY =>
        --             nxt.operand.now := nxt.operand.op1Now;
--            when OP_ALWAYS =>
--              nxt.operand.now := '1';
--            when OP_INTERVAL =>
--              nxt.operand.now := nxt.operand.op1Now and (not nxt.operand.op2Now);
--            when OP_SINCE =>
--              nxt.operand.now := nxt.operand.op2Now;
--            when OP_END_SEQUENCE =>
--              nxt.initialized := '1';
--              o.calc_finish <= '1';
--              nxt.startup_cnt := i.reg.interval.min & i.reg.interval.max;
--            when others =>
--              null;
--          end case;

--        else

        case i.reg.command is
          when OP_FALSE =>
            nxt.operand.now := '0';
          when OP_TRUE =>
            nxt.operand.now := '1';
          when OP_ATOMIC =>
            nxt.operand.now := nxt.operand.op1now;
          when OP_NOT =>
            nxt.operand.now := not nxt.operand.op1Now;
          when OP_AND =>
            nxt.operand.now := nxt.operand.op1Now and nxt.operand.op2Now;
          when OP_OR =>
            nxt.operand.now := nxt.operand.op1Now or nxt.operand.op2Now;
          when OP_IMPLICIT =>
            nxt.operand.now := (not nxt.operand.op1Now) or nxt.operand.op2Now;
          when OP_EQUIVALENT =>
            nxt.operand.now := nxt.operand.op1Now xnor nxt.operand.op2Now;
          when OP_PREVIOUSLY =>
            nxt.operand.now := nxt.operand.op1Pre;
          when OP_EVENTUALLY =>
            nxt.operand.now := nxt.operand.op1Now or nxt.operand.pre;
          when OP_ALWAYS =>
            nxt.operand.now := nxt.operand.op1Now and nxt.operand.pre;
          when OP_START =>
            nxt.operand.now := nxt.operand.op1Now and (not nxt.operand.op1Pre);
          when OP_END =>
            nxt.operand.now := (not nxt.operand.op1Now) and nxt.operand.op1Pre;
          when OP_INTERVAL =>
            nxt.operand.now := (not nxt.operand.op2Now) and (nxt.operand.op1Now or nxt.operand.pre);
          when OP_SINCE =>
            nxt.operand.now := nxt.operand.op2Now or (nxt.operand.op1Now and nxt.operand.pre);
          when OP_END_SEQUENCE =>
            -- update violated
            nxt.violated  := not nxt.operand.op1Now;
            o.calc_finish <= '1';
            if this.startup_cnt = std_logic_vector(to_unsigned(0, COMMAND_WIDTH)) then
              nxt.violated_valid := '1';
            else
              nxt.violated_valid := '0';
              nxt.startup_cnt    := this.startup_cnt - 1;
            end if;
          when OP_MTL_BOXBOX |  -- this evaluates the valid boxbox predicate
            OP_MTL_DIAMONDDIAMOND =>
            nxt.state := CALC_MTL;
            finish    := '0';
          when others =>
            finish          := '0';
            o.dotMemory.sel <= '1';
            nxt.state       := GARBAGE;
        end case;
--        end if;

      when GARBAGE =>
        -- run garbage collection
        if i.dotMemory.empty = '0' then
          if i.dotMemory.head.stop.time < this.time_intervalMin then
            o.dotMemory.delete <= '1';
          end if;
        end if;
        nxt.state := UPDATE_LIST;

      when UPDATE_LIST =>
        case this.command is
          when OP_MTL_BOXDOT |
            OP_MTL_DIAMONDDOT =>
            if op1RisingEdge_r = '1' then        -- rising edge
              --select_time               := S_TIME;
              o.dotMemory.timestamp <= i.time;
              o.dotMemory.add_start <= '1';
            elsif op1_falling_edge_r = '1' then  -- falling edge
              --select_time := S_TIME_1;
              nxt.timestamp_buffer.time := this.time_1;
              o.dotMemory.timestamp     <= this.time_1;
              if feasible = '1' then             -- feasible check
                o.dotMemory.add_end <= '1';
              else
                o.dotMemory.drop_tail <= '1';
              end if;
            end if;

          when OP_MTL_SINCE =>
            if this.operand.op1Now = '1' then
              if op2RisingEdge_r = '1' then        -- rising edge
                if i.dotMemory.empty = '0' or i.dotMemory.tail.start.valid = '1' then  -- list is not empty
                  --select_time := S_TIME_1;
                  o.dotMemory.timestamp <= this.time_1;
                  if feasible = '1' then           -- feasible check
                    o.dotMemory.add_end <= '1';
                  else
                    o.dotMemory.drop_tail <= '1';
                  end if;
                end if;
              elsif op2_falling_edge_r = '1' then  -- falling edge
                --select_time           := S_TIME;
                nxt.timestamp_buffer.time := i.time;
                o.dotMemory.timestamp     <= i.time;
                o.dotMemory.add_start     <= '1';
              end if;
            else
              --select_time := S_TIME_1;
              o.dotMemory.timestamp <= this.time_1;
              if this.operand.op2Now = '1' then
                -- note => in the paper n must not be 0 in this when, in this implementation this cannot happen
                o.dotMemory.set_tail <= '1';
              else
                o.dotMemory.reset_tail <= '1';
              end if;
            end if;
          when others =>
            null;
        end case;

        nxt.state := CALC_MTL;

      when CALC_MTL =>
        case this.command is
          when OP_MTL_BOXBOX |  -- this evaluates the valid boxbox predicate
            OP_MTL_DIAMONDDIAMOND =>
            if op1RisingEdge_r = '1' then        -- rising edge
              nxt.timestamp_buffer.valid := '1';
              --nxt.timestampBuffethis.start.time := this.time;
              --select_time                := S_TIME;
              nxt.timestamp_buffer.time  := i.time;
              o.boxMemory.write          <= '1';
            elsif op1_falling_edge_r = '1' then  -- falling edge
              nxt.timestamp_buffer.valid := '0';
              --nxt.timestampBuffethis.start.time := time_1;
              --select_time                := S_TIME_1;
              --nxt.timestamp_buffer.time := this.time_1;
              --o.dotMemory.timestamp     <= this.time_1;
              o.boxMemory.write          <= '1';
            else
              nxt.timestamp_buffer := slv_to_ts(i.boxMemory.rdData);
            end if;

            if nxt.timestamp_buffer.valid = '0' then
              nxt.operand.now := '0';
            else
              if this.time_intervalMax >= nxt.timestamp_buffer.time then
                nxt.operand.now := '1';
              else
                nxt.operand.now := '0';
              end if;
            end if;
          when OP_MTL_BOXDOT |  -- this evaluates the valid boxdot predicate
            OP_MTL_DIAMONDDOT |
            OP_MTL_SINCE =>

            -- the first conjunct
            if i.dotMemory.head.start.valid = '0' then  -- we have not received an edge yet
              first_conjunct := '0';
            else
              if i.dotMemory.head.start.time <= this.time_intervalMax then
                first_conjunct := '1';
              else
                first_conjunct := '0';
              end if;
            end if;

            -- the second conjunct
            if i.dotMemory.head.stop.valid = '0' then  -- t.end is infinite
              second_conjunct := '1';
            else
              if i.dotMemory.head.stop.time >= this.time_intervalMin then
                second_conjunct := '1';
              else
                second_conjunct := '0';
              end if;
            end if;

            if this.command = OP_MTL_SINCE then
              nxt.operand.now := not (first_conjunct and second_conjunct);
            else
              nxt.operand.now := first_conjunct and second_conjunct;
            end if;
          when others =>
            null;
        end case;

        finish := '1';

      when STALL =>
        finish := '1';

    end case;

--    case select_time is
--      when S_TIME =>
--        nxt.timestamp_buffer.time := i.time;
--        o.dotMemory.timestamp     <= i.time;
--      when S_TIME_1 =>
--        nxt.timestamp_buffer.time := this.time_1;
--        o.dotMemory.timestamp     <= this.time_1;
--      when others =>
--        null;
--    end case;

    case nxt.command is
      when OP_MTL_DIAMONDDIAMOND |
        OP_MTL_DIAMONDDOT =>
        nxt.reg.result := not nxt.operand.now;
      when others =>
        nxt.reg.result := nxt.operand.now;
    end case;

    if finish = '1' then
      nxt.state := STALL;

      if i.nxt_ack = '1' then
        if i.prev_fin = '1' then
          nxt.state := CALC;
          o.ack     <= '1';
        else
          nxt.state := IDLE;
        end if;
      end if;
    end if;

    o.boxMemory.wrData <= ts_to_slv(nxt.timestamp_buffer);
    o.resultNow        <= nxt.reg.result;
    o.initialized      <= this.initialized;
    o.fin              <= finish;
    o.reg              <= this.reg;
    this_nxt           <= nxt;
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
