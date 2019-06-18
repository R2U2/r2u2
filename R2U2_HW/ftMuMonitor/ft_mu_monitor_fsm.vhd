-------------------------------------------------------------------------------
-- Project    : CevTes RVU (Runtime Verification Unit)
-------------------------------------------------------------------------------
-- File       : mu_monitor_fsm.vhd
-- Author     : Andreas Hagmann (ahagmann@ecs.tuwien.ac.at)
-- Copyright  : 2011, Thomas Reinbacher (treinbacher@ecs.tuwien.ac.at)
--              Vienna University of Technology, ECS Group
-------------------------------------------------------------------------------
-- Fixed by ISU RCL 2017
-------------------------------------------------------------------------------
-- Description: A state machine for mu_monitor calculation.
-- PAMO:   op1Type unterscheidet typen des inputs wie ich es verstehe --> 
--         der bug dass es nur mit atomics geht koennte hier gesucht werden
-------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.cevLib_unsigned_pkg.all;
use work.math_pkg.all;
use work.mu_monitor_pkg.all;
use work.ft_mu_monitor_pkg.all;
use work.log_input_pkg.all;
use work.ram_pkg.all;


--port(
--    clk                     : in  std_logic;  -- clock signal
--    res_n                   : in  std_logic;  -- reset signal (active low)
--    trigger                 : in  std_logic;
--    atomics                 : in  std_logic_vector(ATOMICS_WIDTH - 1 downto 0);  -- invariant-checker-violated-bits from fifo
--    timestamp               : in  std_logic_vector(TIMESTAMP_WIDTH - 1 downto 0);  -- invariant-checker-violated-bits from fifo
--    imemAddr                : out std_logic_vector(log2c(ROM_LEN) - 1 downto 0);
--    imemData                : in  std_logic_vector(COMMAND_WIDTH - 1 downto 0);
--    interval_memory_data    : in  std_logic_vector(2*TIMESTAMP_WIDTH - 1 downto 0);
--    interval_memory_addr    : out std_logic_vector(log2c(INTERVAL_MEMORY_LEN)-1 downto 0);
--    async_out               : out ft_tuple_t;
--    finish                  : out std_logic;
--    data_memory_async_data  : out std_logic_vector(FT_TUPLE_T_LEN-1+1 downto 0);
--    data_memory_async_empty : out std_logic;
--    data_memory_addr        : in  std_logic_vector(log2c(ROM_LEN) - 1 downto 0);
    
----Pei: signal for simulation to replace spy function
--    this_new_result         : out  std_logic;
--    this_sync_out_data_time  : out std_logic_vector(TIMESTAMP_WIDTH - 1 downto 0)
--    );
entity ft_mu_monitor_fsm is
  port (clk                     : in  std_logic;  -- clock signal
    res_n                   : in  std_logic;  -- reset signal (active low)
    violated                : out std_logic;  -- violated signal (result is not correct)
    violatedValid           : out std_logic;
    trigger                 : in  std_logic;
    atomics                 : in  std_logic_vector(ATOMICS_WIDTH-1 downto 0);  -- invariant-checker-violated-bits from fifo
    timestamp               : in  std_logic_vector(TIMESTAMP_WIDTH-1 downto 0);  -- invariant-checker-violated-bits from fifo
    imemAddr                : out std_logic_vector(log2c(ROM_LEN) -1 downto 0);
    imemData                : in  std_logic_vector(COMMAND_WIDTH-1 downto 0);
    interval_memory_data    : in  std_logic_vector(2*TIMESTAMP_WIDTH-1 downto 0);
    interval_memory_addr    : out std_logic_vector(log2c(INTERVAL_MEMORY_LEN) -1 downto 0);
    pt_data_memory_addr     : out std_logic_vector(log2c(DATA_MEMORY_LEN) -1 downto 0);
    pt_data_memory_data     : in  std_logic;
    sync_out                : out ft_logic_t;
    async_out               : out ft_tuple_t;
    finish                  : out std_logic;
    data_memory_async_data  : out std_logic_vector(FT_TUPLE_T_LEN-1+1 downto 0);
    data_memory_async_empty : out std_logic;
    data_memory_sync_data   : out ft_logic_t;
    data_memory_addr        : in  std_logic_vector(log2c(ROM_LEN) - 1 downto 0);
    
    this_new_result         : out  std_logic;
    this_sync_out_data_time : out std_logic_vector(TIMESTAMP_WIDTH - 1 downto 0);

--signal for debug
    debug : out debug_t    
    --have_new_result : out std_logic;
    --new_result_rdy : out std_logic;
    --new_result : out ft_tuple_t;
    --command : out operator_t;
    --interval_max : out this.interval.max
    --pc_debug : out std_logic_vector(log2c(ROM_LEN) - 1 downto 0);
    --have_new_result_intermediate : out std_logic;
    --new_result_rdy_intermediate : out std_logic
    );
end entity;

architecture arch of ft_mu_monitor_fsm is
  -- data types
  type state_t is (RESET, IDLE, FETCH, LOAD_OP_WAIT, LOAD_OP_CHECKING, LOAD_OP, CALC, WRITE_BACK, INC_PC);

  type registerType is record
    state                     : state_t;
    programCounter            : std_logic_vector(log2c(ROM_LEN) - 1 downto 0);
    command                   : instruction_t;
    atomics                   : std_logic_vector(ATOMICS_WIDTH-1 downto 0);
    time                      : std_logic_vector(TIMESTAMP_WIDTH-1 downto 0);
    interval                  : interval_t;
    interval_length           : std_logic_vector(TIMESTAMP_WIDTH - 1 downto 0);
    op1                       : ft_queue_async_out_t;
    op2                       : ft_queue_async_out_t;
    result                    : ft_tuple_t;
    new_result                : std_logic;
    async_out                 : ft_tuple_t;
  end record;

  -- variables / constants

  signal registerReset : registerType := (
    RESET,
    (std_logic_vector(to_unsigned(0,log2c(ROM_LEN)))),--(others => '0'),
    INSTRUCTION_T_NULL,
    (others => '0'),
    (others => '1'),
    INTERVAL_T_NULL,
    (others => '0'),
    FT_QUEUE_ASYNC_OUT_T_NULL,
    FT_QUEUE_ASYNC_OUT_T_NULL,
    FT_TUPLE_T_NULL,
    '0',
    FT_TUPLE_T_NULL
    );

  signal this, nxt : registerType;

  signal op1Type : std_logic_vector(2-1 downto 0);
  signal op2Type : std_logic_vector(2-1 downto 0);
  signal atomic_1 : std_logic;
  signal atomic_2 : std_logic;
  signal last_value : std_logic;
  signal s_reg_data : sr_t;
  signal s_reg_temp : sr_t;
  signal sr_addr : std_logic_vector(log2c(NUMBER_OF_QUEUES)-1 downto 0);
  signal sr_wrData : std_logic_vector(SR_DATA_WIDTH-1 downto 0);
  signal sr_write : std_logic;
  signal sr_rdData : std_logic_vector(SR_DATA_WIDTH-1 downto 0);
  signal queue_i : ft_queue_in_t;
  signal queue_o : ft_queue_out_t;
  signal pip_cout : std_logic_vector(4 downto 0);
  signal op1 : ft_tuple_t;
  signal op2 : ft_tuple_t;
  signal pc : std_logic_vector(log2c(ROM_LEN) - 1 downto 0);

  signal box_result_time : std_logic_vector(TIMESTAMP_WIDTH-1 downto 0);
  signal new_result_rdy_box : std_logic;
  signal have_new_result_box : std_logic;
  signal op1_temp : std_logic_vector(TIMESTAMP_WIDTH downto 0);
  signal op2_temp : std_logic_vector(TIMESTAMP_WIDTH downto 0);
  signal finish_sig : std_logic;

  signal rst_finish : std_logic;
  signal sr_addr_cnt : std_logic_vector(sr_addr'length downto 0);--should be 1 bit wider than sr_addr
  signal sr_addr_reset : std_logic_vector(sr_addr'length-1 downto 0);



begin
  

  violated <= '0';
  violatedValid <= '0';
  pt_data_memory_addr <= (others=>'0');
  sync_out <= FT_MAYBE;
  data_memory_sync_data <= FT_MAYBE;
--pei: added the statement 
  this_new_result <= this.new_result;
  this_sync_out_data_time <= this.async_out.time;
  --this_sync_out_data_value <= this.sync_out.data.value;
--signal for debugging (Dr.Jones wants to see this)
  debug.have_new_result_intermediate <= queue_i.have_new_result;
  debug.new_result_rdy_intermediate <= queue_i.new_result_rdy;
  debug.pc_debug <= pc;
-----------
  debug.have_new_result <= queue_i.have_new_result when this.command.command=OP_END_SEQUENCE else '0';
  debug.new_result_rdy <= queue_i.new_result_rdy when this.command.command=OP_END_SEQUENCE else '0';
  debug.new_result <= queue_i.new_result;
  debug.command <= this.command.command;
  debug.interval <= this.interval;
  debug.finish <= finish_sig;
  -- instantiate components    
  finish <= finish_sig;

  i_queue : ft_queue
    port map (
      clk => clk,
      res_n => res_n,
      i => queue_i,
      o => queue_o,
      map_rdAddr => (others=>'0'),
      map_wrAddr => (others=>'0')
      );
  -- logic
  combination : process(res_n, this, atomics, timestamp, imemData, interval_memory_data, trigger, data_memory_addr,
    queue_i.new_result_rdy, queue_o, rst_finish)


  begin

    if (res_n = '0') then
      nxt <= registerReset;

    else
      nxt <= this;

      -- default values for signals and variables
      imemAddr                  <= this.programCounter;
      finish_sig                <= '0';
      async_out                 <= this.async_out;

      op1Type <= this.command.op1.is_memory_addr & this.command.op1.is_immediate;
      op2Type <= this.command.op2.is_memory_addr & this.command.op2.is_immediate;

      interval_memory_addr <= this.command.intervalAddr(interval_memory_addr'length - 1 downto 0);
      

      -- fsm
      case this.state is
        when RESET =>
          if(rst_finish='1')then
            nxt.state          <= IDLE;
          end if;
          
        when IDLE =>
          nxt.new_result <= '0';
          nxt.programCounter <= (others => '0');
          imemAddr           <= (others => '0');--instruction memory address
          if trigger = '1' then           -- start new run
            nxt.state <= FETCH;
          end if;
          
        when FETCH =>
          nxt.new_result <= '0';
          finish_sig <= '0';
          nxt.atomics <= atomics;
          nxt.command <= slv_to_instruction(imemData);
          nxt.time    <= timestamp;--Pei: ??
          nxt.state   <= LOAD_OP_WAIT;
          nxt.programCounter <= this.programCounter + 1;
        when LOAD_OP_WAIT =>
          if(queue_o.state = FETCH_RD)then
            nxt.state <= LOAD_OP_CHECKING;
          end if;

        when LOAD_OP_CHECKING =>
          if(queue_o.state=WAIT_NEW_RESULT)then
            nxt.state <= LOAD_OP;
          end if;
          if(queue_o.state=IDLE)then--no new result because of no new input
            nxt.state <= INC_PC;
          end if;
        when LOAD_OP =>
          case op1Type is
            when "10" => --read from queue
              nxt.op1.tail <= op1;
            when "00" => -- read atomic
              nxt.op1.tail.value <= this.atomics(conv_to_integer(this.command.op1.value(log2c(ATOMICS_WIDTH)-1 downto 0)));
              nxt.op1.tail.time  <= timestamp; 
            when others =>
              null;
          end case;
          case op2Type is
            when "10" => --read from queue
              nxt.op2.tail <= op2;        
            when "00" => -- read atomic
              nxt.op2.tail.value <= this.atomics(conv_to_integer(this.command.op2.value(log2c(ATOMICS_WIDTH)-1 downto 0)));
              nxt.op2.tail.time  <= timestamp; 
            when others =>
              null;
          end case;
          -- load timestamps
          nxt.interval.min <= interval_memory_data(2*TIMESTAMP_WIDTH-1 downto TIMESTAMP_WIDTH);
          nxt.interval.max <= interval_memory_data(TIMESTAMP_WIDTH-1 downto 0);
    
          nxt.state <= CALC;

        when CALC =>
          if(queue_i.new_result_rdy='1')then
            nxt.state      <= WRITE_BACK;
          end if;

          case this.command.command is
            when OP_LOAD =>
              
            when OP_END_SEQUENCE => 
              nxt.async_out  <= this.op1.head;
              
            when OP_FT_BOXBOX |
              OP_FT_DIAMONDDIAMOND |
              OP_FT_BOXDOT |
              OP_FT_DIAMONDDOT =>

              case this.command.command is
                when OP_FT_BOXBOX =>
                  
                when OP_FT_DIAMONDDIAMOND =>
                
                  
                when OP_FT_BOXDOT | OP_FT_DIAMONDDOT =>
                  
                when others =>
                  null;
              end case;
              
            when OP_FT_UNTIL =>
              
              
            when OP_FT_NOT =>
              
            when OP_FT_AND =>
              
            when OP_FT_IMPLICIT =>

            when others =>
              null;
          end case;
          
        
        when WRITE_BACK =>
          if((queue_o.state=WRITE_NEW_RESULT_AND_PTR or queue_o.state=UPDATE_PTR) and queue_o.ptr_write='1')then
            if(queue_o.doSelfLoop='0')then-------------------------------tmp:new feature
              nxt.state <= INC_PC;
            else
              nxt.state <= LOAD_OP_WAIT;--correct??
            end if;
          end if;
          
          
        when INC_PC =>
          nxt.new_result <= '1';
          case this.command.command is
            when OP_END_SEQUENCE=>
              nxt.state <= IDLE;
              finish_sig <= '1';
            when others=>
              nxt.state <= FETCH;
          end case;
        when others =>
          null;
      end case;

      -- precalculations
      nxt.interval_length <= this.interval.max - this.interval.min;
    end if;

  end process;

  --queue_i.state <= this.state;
  queue_i.pc <= pc;
--op1 <= queue_o.op1;
--op2 <= queue_o.op2;
  op1_temp <= atomic_1 & timestamp;
  op2_temp <= atomic_2 & timestamp;
  op1 <= slv_to_ts(op1_temp) when queue_i.is_op1_atomic='1' else queue_o.op1;
  op2 <= slv_to_ts(op2_temp) when queue_i.is_op2_atomic='1' else queue_o.op2;
  s_reg_data <= slv_to_sr(sr_rdData);
  sr_addr <=  sr_addr_reset when this.state=RESET else pc;


  reg : process (clk , res_n)
  begin
    if res_n = '0' then
      pc <= (others => '0');
      this <= registerReset;
      queue_i.opNum_rdy <= '0';
      queue_i.new_result_rdy <= '0';
      --queue_i.is_load_command <= '0';
      queue_i.command <= OP_START;
      queue_i.need_op2 <= '0';
      queue_i.new_result <= FT_TUPLE_T_NULL;
      queue_i.is_op1_atomic <= '0';
      queue_i.is_op2_atomic <= '0';
      queue_i.have_new_result <= '0';
      queue_i.op1_num <= (others=>'0');
      queue_i.op2_num <= (others=>'0');
      have_new_result_box <= '0';
      new_result_rdy_box <= '0';
      box_result_time <= (others=>'0');
      atomic_1 <= '0';
      atomic_2 <= '0';
      s_reg_temp <= SR_T_NULL;
      sr_write <= '0';
      sr_wrData <= (others => '0');
      pip_cout <= (others => '0');
      
      rst_finish <= '0';
      sr_addr_cnt <= (others=>'0');
      sr_addr_reset <= (others=>'0');

    elsif rising_edge (clk) then
      this <= nxt;
      sr_write <= '0';
      rst_finish <= '0';
      case this.state is 
        when RESET =>
          if(unsigned(sr_addr_cnt)=NUMBER_OF_QUEUES)then
            sr_wrData <=  (others=>'0');
            rst_finish <= '1';
            sr_addr_reset <= (others=>'0');
            sr_addr_cnt <= (others=>'0');
            sr_write <= '0';
          else
            sr_addr_cnt <= std_logic_vector(unsigned(sr_addr_cnt)+1);
            sr_addr_reset <= sr_addr_cnt(sr_addr_reset'length-1 downto 0);
            sr_wrData <= (others=>'0');
            sr_write <= '1';
          end if;

        when IDLE =>
          pc <= (others=>'0');
        when FETCH =>
          queue_i.op1_num <= nxt.command.op1.value(queue_i.op1_num'length - 1 downto 0);
          queue_i.op2_num <= nxt.command.op2.value(queue_i.op2_num'length - 1 downto 0);
          queue_i.command <= nxt.command.command;
          
        when LOAD_OP_WAIT =>

          s_reg_temp <= s_reg_data;

          if(this.command.command=OP_FT_AND or this.command.command=OP_FT_UNTIL)then
            queue_i.need_op2 <= '1';
          end if;
          if(op1Type="00")then
            queue_i.is_op1_atomic <= '1';
            atomic_1 <= this.atomics(conv_to_integer(this.command.op1.value(log2c(ATOMICS_WIDTH)-1 downto 0)));
          else 
            queue_i.is_op1_atomic <= '0';
          end if;
          if(op2Type="00")then
            queue_i.is_op2_atomic <= '1';
            atomic_2 <= this.atomics(conv_to_integer(this.command.op2.value(log2c(ATOMICS_WIDTH)-1 downto 0)));
          else
            queue_i.is_op2_atomic <= '0';
          end if;
          queue_i.opNum_rdy <= '1';

        when LOAD_OP_CHECKING =>
          queue_i.opNum_rdy <= '0'; 
          
        when LOAD_OP =>

        when CALC =>
          case this.command.command is
            ----------------------------------------------------------------------
            when OP_LOAD =>
              queue_i.new_result_rdy <= '1';
              if(queue_o.isEmpty_1='0')then
                queue_i.have_new_result <= '1';
                queue_i.new_result <= op1;
              end if;
            ----------------------------------------------------------------------
            when OP_END_SEQUENCE =>
              queue_i.new_result_rdy <= '1';
              if(queue_o.isEmpty_1='0')then
                queue_i.have_new_result <= '1';
                queue_i.new_result <= op1;
              end if;
            ----------------------------------------------------------------------
            when OP_FT_NOT =>
              queue_i.new_result_rdy <= '1';
              if(queue_o.isEmpty_1='1')then
                queue_i.have_new_result <= '0';
              else
                queue_i.new_result.value <= not op1.value;
                queue_i.new_result.time <= op1.time;
                queue_i.have_new_result <= '1';
              end if;
            ----------------------------------------------------------------------
            when OP_FT_BOXBOX =>--This operation is no longer supported, use OP_FT_BOTDOT
              --queue_i.new_result_rdy <= '1';
              --if(queue_o.isEmpty_1='0')then
              --  queue_i.new_result <= op1;
              --  s_reg_temp.last_value <= op1.value;
              --  queue_i.have_new_result <= '1';
              --  if(op1.value='1' and s_reg_data.last_value='0')then
              --    s_reg_temp.mUp <= s_reg_data.mPre;
              --  end if;
              --  s_reg_temp.mPre <= std_logic_vector(unsigned(op1.time(mPre_DATA_WIDTH-1 downto 0)) + 1);
              --  if(op1.value='1')then
              --    if (s_reg_data.last_value='0' and unsigned(s_reg_data.mPre)+unsigned(this.interval.max)<=unsigned(op1.time)) or 
              --     (s_reg_data.last_value='1' and unsigned(s_reg_data.mUp)+unsigned(this.interval.max)<=unsigned(op1.time)) then
              --      queue_i.new_result.time <= std_logic_vector(unsigned(op1.time)-unsigned(this.interval.max));    
              --      --queue_i.have_new_result <= '1';
              --      --s_reg_temp.last_value <= '1';
              --    else 
              --      queue_i.have_new_result <= '0';
              --      --s_reg_temp.last_value <= '1';--last_value=???, depends on how we inteprete line 3
              --    end if;
              --  end if;
              --else 
              --  queue_i.have_new_result <= '0';
              --  --s_reg_temp.last_value <= '0';--last_value=???, depends on how we inteprete line 3
              --end if;
            ----------------------------------------------------------------------
            when OP_FT_AND =>
              queue_i.new_result_rdy <= '1';
              if(queue_o.isEmpty_1='0' and queue_o.isEmpty_2='0')then
                if(op1.value='1' and op2.value='1')then
                  queue_i.have_new_result <= '1';
                  queue_i.new_result.value <= '1';
                  if unsigned(op1.time) < unsigned(op2.time)then
                    queue_i.new_result.time <= op1.time;
                  else 
                    queue_i.new_result.time <= op2.time;
                  end if;
                --elsif(op1.value='0' and op2.value='0')then
                else
                  queue_i.have_new_result <= '1';
                  queue_i.new_result.value <= '0';
                  if(op1.value='0' and op2.value='0')then 
                    if(unsigned(op1.time) < unsigned(op2.time))then
                      queue_i.new_result.time <= op2.time;
                    else 
                      queue_i.new_result.time <= op1.time;
                    end if;
                  elsif(op1.value='0')then
                    queue_i.new_result.time <= op1.time;
                  elsif(op2.value='0')then
                    queue_i.new_result.time <= op2.time;
                  end if;
                end if;
              elsif(queue_o.isEmpty_1='0' and queue_o.isEmpty_2='1')then--Line 6
                if(op1.value='0')then
                  queue_i.have_new_result <= '1';
                  queue_i.new_result <= op1;
                end if;
              elsif(queue_o.isEmpty_1='1' and queue_o.isEmpty_2='0')then --queue_o.isEmpty_1='1', line 8
                if(op2.value='0')then
                  queue_i.have_new_result <= '1';
                  queue_i.new_result <= op2;
                end if;
              end if;
            ----------------------------------------------------------------------
            when OP_FT_BOXDOT =>
            -- Update: split the pipeline
              -- s_reg_temp.mUp s_reg_data.mPre s_reg_data.last_value
              -- m, tau_pre, v_pre


              if(unsigned(pip_cout)=0)then
                if(queue_o.isEmpty_1='1')then
                  pip_cout <= std_logic_vector(to_unsigned(10,pip_cout'length));
                  queue_i.new_result_rdy <= '1';
                else
                  s_reg_temp.t_pre <= op1.time;
                  s_reg_temp.v_pre <= op1.value;
                  if(op1.value='1' and s_reg_data.v_pre='0' and s_reg_data.m /= s_reg_data.t_pre)then
                    s_reg_temp.m <= std_logic_vector(unsigned(s_reg_data.t_pre)+1);
                  else
                    s_reg_temp.m <= s_reg_data.m;
                  end if;
                  pip_cout <= std_logic_vector(to_unsigned(1,pip_cout'length));
                end if;
              elsif (unsigned(pip_cout)=1) then
                if(op1.value='1')then
                  if(unsigned(op1.time)+unsigned(this.interval.min)>=unsigned(s_reg_temp.m)+unsigned(this.interval.max))then
                    pip_cout <= std_logic_vector(to_unsigned(2,pip_cout'length));--check if result time <0
                  else
                    queue_i.new_result_rdy <= '1';
                    pip_cout <= std_logic_vector(to_unsigned(10,pip_cout'length));
                    queue_i.have_new_result <= '0';
                    
                  end if;
                else
                  if(unsigned(op1.time) >= unsigned(this.interval.min))then
                    queue_i.new_result.time <=  std_logic_vector(unsigned(op1.time)-unsigned(this.interval.min));
                    queue_i.new_result.value <= '0';
                    queue_i.have_new_result <= '1';
                  else                     
                    queue_i.have_new_result <= '0';
                  end if;
                  queue_i.new_result_rdy <= '1';
                  pip_cout <= std_logic_vector(to_unsigned(10,pip_cout'length));                    
                end if;
              elsif(unsigned(pip_cout)=2) then
                if(unsigned(op1.time)>=unsigned(this.interval.max))then
                  queue_i.new_result.time <=  std_logic_vector(unsigned(op1.time)-unsigned(this.interval.max));
                  queue_i.new_result.value <= '1';
                  queue_i.have_new_result <= '1';
                else
                  queue_i.have_new_result <= '0';
                end if;
                queue_i.new_result_rdy <= '1';
                pip_cout <= std_logic_vector(to_unsigned(10,pip_cout'length));
              end if;



              --if(new_result_rdy_box='0')then
              --  new_result_rdy_box <= '1';
              --  if(queue_o.isEmpty_1='0')then
              --    queue_i.new_result <= op1;
              --    s_reg_temp.last_value <= op1.value;
              --    box_result_time <= op1.time;
              --    have_new_result_box <= '1';
              --    if(op1.value='1' and s_reg_data.last_value='0')then
              --      s_reg_temp.mUp <= s_reg_data.mPre;
              --    end if;
              --    s_reg_temp.mPre <= std_logic_vector(unsigned(op1.time(mPre_DATA_WIDTH-1 downto 0)) + 1);
              --    if(op1.value='1')then
              --      if (s_reg_data.last_value='0' and unsigned(s_reg_data.mPre)+unsigned(this.interval.max)<=unsigned(op1.time)+unsigned(this.interval.min)) or 
              --       (s_reg_data.last_value='1' and unsigned(s_reg_data.mUp)+unsigned(this.interval.max)<=unsigned(op1.time)+unsigned(this.interval.min)) then
              --        queue_i.new_result.time <= std_logic_vector(unsigned(op1.time)+unsigned(this.interval.min)-unsigned(this.interval.max));
              --        box_result_time <=  std_logic_vector(unsigned(op1.time)+unsigned(this.interval.min)-unsigned(this.interval.max));
              --      else 
              --        have_new_result_box <= '0';
              --      end if;
              --    end if;
              --  else 
              --    have_new_result_box <= '0';
              --  end if; 
              --end if;
              ----------------------------------------------
              --if(new_result_rdy_box='1')then
              --  queue_i.new_result_rdy <= '1';

              --  if(have_new_result_box='1' and unsigned(box_result_time)>=unsigned(this.interval.min))then
      
              --    queue_i.new_result.time <= std_logic_vector(unsigned(box_result_time)-unsigned(this.interval.min)); 
              --    queue_i.have_new_result <= '1';
              --  end if;
              --end if;
            ----------------------------------------------------------------------  
            when OP_FT_UNTIL =>--op1.time == op2.time

              if(unsigned(pip_cout)=0)then
                if(queue_o.isEmpty_1='0' and queue_o.isEmpty_2='0')then
                  pip_cout <= std_logic_vector(to_unsigned(1,pip_cout'length));
                  s_reg_temp.v_pre <= op2.value;
                  s_reg_temp.t_pre <= op2.time;
                else -- no new output
                  queue_i.new_result_rdy <= '1';
                  queue_i.have_new_result <= '0';
                  pip_cout <= std_logic_vector(to_unsigned(10,pip_cout'length));
--                  s_reg_temp.v_pre <= s_reg_data.v_pre;--
--                  s_reg_temp.t_pre <= s_reg_data.t_pre;--
--                  s_reg_temp.m <= s_reg_data.m;--
                end if;
              elsif(unsigned(pip_cout)=1)then
                if(s_reg_data.v_pre = '1' and op2.value = '0')then
                  s_reg_temp.m <= std_logic_vector(unsigned(s_reg_data.t_pre)+1);
                else
                  s_reg_temp.m <= s_reg_data.m;
                end if;
                queue_i.new_result.time <= std_logic_vector(unsigned(op1.time)-unsigned(this.interval.min));
                if(op2.value = '1')then
                  queue_i.new_result.value <= '1'; 
                  pip_cout <= std_logic_vector(to_unsigned(4,pip_cout'length));
                elsif(op1.value = '0')then
                  queue_i.new_result.value <= '0';
                  pip_cout <= std_logic_vector(to_unsigned(4,pip_cout'length));
                else 
                  pip_cout <= std_logic_vector(to_unsigned(2,pip_cout'length));
                  queue_i.new_result.time <= std_logic_vector(unsigned(op1.time)+unsigned(this.interval.min));--serve as temp register
                end if; 
              elsif (unsigned(pip_cout)=2) then
                queue_i.new_result.time <= std_logic_vector(unsigned(op1.time)-unsigned(this.interval.max));
                queue_i.new_result_rdy <= '1';
                pip_cout <= std_logic_vector(to_unsigned(10,pip_cout'length));
                if(unsigned(queue_i.new_result.time)>=unsigned(this.interval.max)+unsigned(s_reg_temp.m))then
                  queue_i.new_result.value <= '0'; -- '0' for strong until. '1' for weak until
                  queue_i.have_new_result <= '1';
                end if;
              elsif (unsigned(pip_cout)=4) then
                queue_i.new_result_rdy <= '1';
                pip_cout <= std_logic_vector(to_unsigned(10,pip_cout'length));
                if(unsigned(op1.time)>=unsigned(this.interval.min))then
                  queue_i.have_new_result <= '1';
                end if;


              end if;
                




              --queue_i.new_result_rdy <= '1';
              --if(queue_o.isEmpty_1='0' and queue_o.isEmpty_2='0')then
              --  if(s_reg_data.last_value='1' and op2.value='0')then
              --    s_reg_temp.mPre <= op1.time;
              --  end if;
              --  if(op2.value='1')then
              --    if(unsigned(op1.time)>=unsigned(this.interval.min))then
              --      queue_i.have_new_result <= '1';
              --      queue_i.new_result.time <= std_logic_vector(unsigned(op1.time)-unsigned(this.interval.min));
              --      queue_i.new_result.value <= '1';
              --    end if;
              --  elsif(op1.value='0')then
              --    if(unsigned(op1.time)>=unsigned(this.interval.min))then
              --      queue_i.have_new_result <= '1';
              --      queue_i.new_result.time <= std_logic_vector(unsigned(op1.time)-unsigned(this.interval.min));
              --      queue_i.new_result.value <= '0';
              --    end if;
              --  else
              --    queue_i.new_result.time <= std_logic_vector(unsigned(op1.time)-unsigned(this.interval.max));
              --    queue_i.new_result.value <= '0';
              --    if(s_reg_data.last_value='1')then
              --      if(unsigned(this.interval.min)>=unsigned(this.interval.max))then
              --        if(unsigned(op1.time)>=unsigned(this.interval.max))then
              --          queue_i.have_new_result <= '1';
              --        end if;
              --      end if;
              --    else
              --      if(unsigned(op1.time)+unsigned(this.interval.min)>=unsigned(this.interval.max)+unsigned(s_reg_data.mPre))then
              --        if(unsigned(op1.time)>=unsigned(this.interval.max))then
              --          queue_i.have_new_result <= '1';
              --        end if;
              --      end if;
              --    end if;
              --  end if;
              --  s_reg_temp.last_value <= op2.value;
              --end if;
            -----------------------------------------------------------------------  
            when others =>
          end case;

          if(queue_i.new_result_rdy='1')then--reset complete signal for every opeartion
            new_result_rdy_box <= '0';
            box_result_time <= (others => '0');
            have_new_result_box <= '0';
            queue_i.new_result_rdy <= '0';
            queue_i.have_new_result <= '0';
            pip_cout <= (others=>'0');
          end if;

        when WRITE_BACK =>
          --queue_i.is_load_command <= '0';
          --this.programCounter <= std_logic_vector(unsigned(this.programCounter)+1);
          if(this.command.command=OP_FT_BOXBOX or this.command.command=OP_FT_BOXDOT or this.command.command=OP_FT_UNTIL)then
            --sr_wrData <= sr_to_slv(s_reg_temp.last_value, s_reg_temp.mUp, s_reg_temp.mPre);
            sr_wrData <= sr_to_slv( s_reg_temp.m, s_reg_temp.t_pre, s_reg_temp.v_pre);
            sr_write <= '1';
          end if;
          --queue_i.need_op2 <= '0';
          
        when INC_PC =>
          queue_i.need_op2 <= '0';
          pc <= std_logic_vector(unsigned(pc)+1);
        when others =>
      end case;

    end if;
  end process;


--The status_reg RAM need to reset all the content to "0"
--mts use the same location as mpre
  status_reg : sp_ram_wt
    generic map(
      ADDR_WIDTH => log2c(NUMBER_OF_QUEUES),
      DATA_WIDTH => SR_DATA_WIDTH
      )
    port map(
      clk    => clk,
      addr   => sr_addr,
      wrData => sr_wrData,
      write  => sr_write,
      rdData => sr_rdData
      );

end architecture;
