-------------------------------------------------------------------------------
-- Project    : CevTes RVU (Runtime Verification Unit)
-------------------------------------------------------------------------------
-- File       : ft_queue.vhd
-- Author     : Andreas Hagmann (ahagmann@ecs.tuwien.ac.at)
-- Copyright  : 2012, Thomas Reinbacher (treinbacher@ecs.tuwien.ac.at)
--              Vienna University of Technology, ECS Group
-------------------------------------------------------------------------------
-- Fixed by ISU RCL 2017
-------------------------------------------------------------------------------
-- Description: provides configurable queues (circular buffers)
-------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pkg.all;
use work.cevlib_unsigned_pkg.all;
use work.ft_mu_monitor_pkg.all;
use work.ram_pkg.all;
use work.mu_monitor_pkg.all;

entity ft_queue is
  port (
    clk                : in  std_logic;
    res_n              : in  std_logic;
    i                  : in  ft_queue_in_t;
    o                  : out ft_queue_out_t;
    map_rdAddr          : in std_logic_vector(log2c(ROM_LEN)-1 downto 0);
    map_wrAddr          : in std_logic_vector(log2c(ROM_LEN)-1 downto 0);
    map_sync_data       : out std_logic_vector(ft_logic_t'LENGTH-1 downto 0);
    map_async_data      : out std_logic_vector(FT_TUPLE_T_LEN-1+1 downto 0)
    );
end entity;

architecture arch of ft_queue is

  type reg_t is record
    state               : queue_state_t;
    op1_wrptr_rdy       : std_logic;
    op2_wrptr_rdy       : std_logic;
    queue_1_inc_finish  : std_logic;
    queue_2_inc_finish  : std_logic;
    no_new_input        : std_logic;
  end record;
  signal this, nxt : reg_t;
  signal registerReset : reg_t :=(
    RESET, 
    '0',
    '0',
    '0',
    '0',
    '0'
    );


  signal wrPtr : std_logic_vector(log2c(QUEUE_SIZE)-1 downto 0);
  --signal last_tau : std_logic_vector(TIMESTAMP_WIDTH-1 downto 0);
  signal last_value : std_logic;
  signal rdPtr_1 : std_logic_vector(log2c(QUEUE_SIZE)-1 downto 0);
  signal rdPtr_2 : std_logic_vector(log2c(QUEUE_SIZE)-1 downto 0);
  signal ptr_inc_1 : std_logic_vector(log2c(QUEUE_SIZE)-1 downto 0);
  signal ptr_inc_2 : std_logic_vector(log2c(QUEUE_SIZE)-1 downto 0);
  signal size_mask : std_logic_vector(log2c(QUEUE_SIZE)-1 downto 0);
  signal lastRd_1 : std_logic_vector(TIMESTAMP_WIDTH-1 downto 0);
  signal lastRd_2 : std_logic_vector(TIMESTAMP_WIDTH-1 downto 0);
  signal op1 : ft_tuple_t;
  signal op2 : ft_tuple_t;

  signal isEmpty_1 : std_logic;
  signal isEmpty_2 : std_logic;
  signal op1_wrptr_reg : std_logic_vector(log2c(QUEUE_SIZE)-1 downto 0);
  signal op2_wrptr_reg : std_logic_vector(log2c(QUEUE_SIZE)-1 downto 0);
  signal queue_data_1 : ft_tuple_t;
  signal queue_data_2 : ft_tuple_t;
  

  signal ptr_addr     : std_logic_vector(log2c(NUMBER_OF_QUEUES)-1 downto 0); 
  signal ptr_wrData   : std_logic_vector(3*log2c(QUEUE_SIZE)+1 downto 0); 
  signal ptr_write    : std_logic;
  signal ptr_rdData   : std_logic_vector(3*log2c(QUEUE_SIZE)+1 downto 0); 
  signal ever_write   : std_logic;

  signal rdPtr_1_temp : std_logic_vector(log2c(QUEUE_SIZE)-1 downto 0);
  signal rdPtr_2_temp : std_logic_vector(log2c(QUEUE_SIZE)-1 downto 0);

  signal lastRd_rdData   : std_logic_vector(2*TIMESTAMP_WIDTH-1 downto 0); 
  signal lastRd_addr     : std_logic_vector(log2c(NUMBER_OF_QUEUES)-1 downto 0); 
  signal lastRd_wrData   : std_logic_vector(2*TIMESTAMP_WIDTH-1 downto 0); 
  signal lastRd_write    : std_logic; 

  signal lastRd_wrData_mem : std_logic_vector(2*TIMESTAMP_WIDTH-1 downto 0); --mem signal to remember last status, for loop operation
  signal isFirstLoop : std_logic;
  signal doselfloop : std_logic;

  signal data_addr_1    : std_logic_vector(log2c(NUMBER_OF_QUEUES)+log2c(QUEUE_SIZE)-1 downto 0); 
  signal data_addr_2    : std_logic_vector(log2c(NUMBER_OF_QUEUES)+log2c(QUEUE_SIZE)-1 downto 0); 
  signal data_wrData  : std_logic_vector(TIMESTAMP_WIDTH downto 0); 
  signal data_write   : std_logic; 
  signal data_wrAddr : std_logic_vector(log2c(NUMBER_OF_QUEUES)+log2c(QUEUE_SIZE)-1 downto 0); 
  signal data_rdData_1  : std_logic_vector(TIMESTAMP_WIDTH downto 0); 
  signal data_rdData_2  : std_logic_vector(TIMESTAMP_WIDTH downto 0); 

  signal debug : std_logic;

  signal rst_finish : std_logic;
  signal rst_finish_1 : std_logic;
  signal rst_finish_2 : std_logic;
  signal lastRd_addr_cnt : std_logic_vector(log2c(NUMBER_OF_QUEUES) downto 0);
  signal data_addr_1_cnt : std_logic_vector(log2c(NUMBER_OF_QUEUES)+log2c(QUEUE_SIZE) downto 0);
  --constant initial_last_value : std_logic_vector(TIMESTAMP_WIDTH-1 downto 0) := (others=>'1');
begin

  --usage structure: [1st read pointer,2nd read pointer,writer pointer,last verdict]
  pointer_inst : sp_ram_wt
    generic map(
      ADDR_WIDTH => log2c(NUMBER_OF_QUEUES),
      DATA_WIDTH => 3*log2c(QUEUE_SIZE)+2
      )
    port map(
      clk    => clk,
      addr   => ptr_addr,
      wrData => ptr_wrData,
      write  => ptr_write,
      rdData => ptr_rdData
      );

  -- last data that the read pointer points to that contributes to an output
  -- new: the time_stamp that we are looking for
  last_rd_inst : sp_ram
    generic map(
      ADDR_WIDTH => log2c(NUMBER_OF_QUEUES),
      DATA_WIDTH => 2*TIMESTAMP_WIDTH
      )
    port map(
      clk    => clk,
      addr   => lastRd_addr,
      wrData => lastRd_wrData,
      write  => lastRd_write,
      rdData => lastRd_rdData
      );

  -- data queue
  data_memory_inst : dp_ram_2w_2r
    generic map(
      ADDR_WIDTH => log2c(NUMBER_OF_QUEUES)+log2c(QUEUE_SIZE),
      DATA_WIDTH => TIMESTAMP_WIDTH + 1
      )
    port map(
      clk     => clk,                     
      rdAddrA => data_addr_1,
      rdAddrB => data_addr_2,
      wrAddr  => data_wrAddr,
      wrData  => data_wrData,
      write   => data_write,
      rdDataA => data_rdData_1,
      rdDataB => data_rdData_2


      --clk      => clk,
      --addr_1   => data_addr_1,
      --addr_2   => data_addr_2,
      --wrData_1 => data_wrData_1,
      --wrData_2 => data_wrData_2,
      --write_1  => data_write_1,
      --write_2  => data_write_2,
      --rdData_1 => data_rdData_1,
      --rdData_2 => data_rdData_2
      );

  combination : process (this, i, res_n, isEmpty_1, isEmpty_2, ptr_write, rst_finish)
  begin
    nxt.state <= this.state;
    if(res_n = '0') then
      nxt <= registerReset;
    else
      
      case this.state is
        when RESET =>
          if(rst_finish = '1')then
            nxt.state <= IDLE;
          end if;
        when IDLE=>
          if(i.opNum_rdy='1')then
            nxt.state <= FETCH_RD;
          end if;
        when FETCH_RD =>
            nxt.state <= NEW_INPUT_CHECK;

        when NEW_INPUT_CHECK =>
          if(i.need_op2='0')then
            if(this.op1_wrptr_rdy='1')then
              nxt.state <= FETCH_PTR;
            end if;
          else 
            if(this.op2_wrptr_rdy='1')then
              nxt.state <= FETCH_PTR;
            end if;
          end if;

        when FETCH_PTR =>
          --if(isEmpty_1='1')then
          --  if(i.need_op2='0' or isEmpty_2='1')then
          --    nxt.state <= UPDATE_PTR;--write the new pointer
          --  end if;
          --end if;
          if(this.queue_1_inc_finish='1' and this.queue_2_inc_finish='1')then
            --if(isEmpty_1='1' and isEmpty_2='1')then
            --  nxt.state <= UPDATE_PTR;
            --else
              nxt.state <= WAIT_NEW_RESULT;
            --end if;
          end if;

        when WAIT_NEW_RESULT =>
          if(i.new_result_rdy='1')then
            if(i.have_new_result='1')then
             nxt.state <= WRITE_NEW_RESULT_AND_PTR;
            else 
              --nxt.state <= IDLE;
              nxt.state <= UPDATE_PTR;
            end if;
          end if;

        when UPDATE_PTR | WRITE_NEW_RESULT_AND_PTR =>
          if(ptr_write='1')then
            nxt.state <= IDLE;
          end if;
        when others =>
          null;
      end case;
    end if;
  end process;

rst_finish <= rst_finish_1 and rst_finish_2;

  reg : process (clk , res_n)
  begin
    if res_n = '0' then
      this <= registerReset;
      op1 <= FT_TUPLE_T_NULL;
      op2 <= FT_TUPLE_T_NULL;
      rdPtr_1_temp <= (others=>'0');
      rdPtr_2_temp <= (others=>'0');
      isEmpty_1 <= '0';
      isEmpty_2 <= '0';
      ptr_inc_1 <= (others=>'0');
      ptr_inc_2 <= (others=>'0');
      op1_wrptr_reg <= (others=>'0');
      op2_wrptr_reg <= (others=>'0');
      data_addr_1 <= (others=>'0');
      data_addr_2 <= (others=>'0');
      data_addr_1_cnt <= (others=>'0');
      --data_wrData_1 <= (others=>'0');
      --data_wrData_2 <= (others=>'0');
      data_wrData <= (others=>'0');---
      data_wrAddr <= (others=>'0');---        
      --data_write_1 <= '0';
      --data_write_2 <= '0';
      data_write <= '0';
      lastRd_wrData <= (others=>'0');
      lastRd_addr <= (others=>'0');
      lastRd_addr_cnt <= (others=>'0');
      lastRd_write <= '0';
      ptr_wrData <= (others=>'0');
      ptr_addr <= (others=>'0');
      ptr_write <= '0';
      debug <= '0';
      isFirstLoop <= '1';
      doSelfLoop <= '0';
      rst_finish_1 <= '0';
      rst_finish_2 <= '0';
    elsif rising_edge (clk) then
      this.state <= nxt.state;
      ptr_write <= '0';
      case this.state is
        when RESET => --need if state to reset all the content of BRAM to 0
          if(rst_finish_1='1' and rst_finish_2='1')then
            rst_finish_1 <= '0';
            rst_finish_2 <= '0';
          else
            if(rst_finish_1 = '0')then
              if(unsigned(lastRd_addr_cnt)=NUMBER_OF_QUEUES)then
                rst_finish_1 <= '1';
                lastRd_addr <= (others=>'0');
                ptr_addr <= (others =>'0');
                lastRd_addr_cnt <= (others=>'0');
                lastRd_write <= '0';
                ptr_write <= '0';
              else
                lastRd_addr_cnt <= std_logic_vector(unsigned(lastRd_addr_cnt)+1);
                lastRd_addr <= lastRd_addr_cnt(lastRd_addr'length-1 downto 0);
                ptr_addr <= lastRd_addr_cnt(lastRd_addr'length-1 downto 0);
                lastRd_wrData <= (others=>'0');
                ptr_wrData <= (others =>'0');
                lastRd_write <= '1';
                ptr_write <= '1';
              end if;
            end if;

            rst_finish_2 <= '1';
            -- -- seems no need to reset data contend
            --if(rst_finish_2='0')then
            --  if(unsigned(data_addr_1_cnt)=DATA_QUEUE_SIZE)then
            --    data_wrAddr <=  (others=>'0');
            --    rst_finish_2 <= '1';
            --    data_addr_1_cnt <= (others=>'0');
            --    data_write <= '0';
            --  else
            --    data_addr_1_cnt <= std_logic_vector(unsigned(data_addr_1_cnt)+1);
            --    data_addr_1 <= data_addr_1_cnt(data_addr_1'length-1 downto 0);
            --    data_wrAddr <= (others=>'0');
            --    data_write <= '1';
            --  end if;
            --end if;

          end if;
          

        when IDLE =>
          isEmpty_1 <= '0';
          isEmpty_2 <= '0';
          debug <= '0';
        when FETCH_RD =>
          lastRd_addr <= i.pc;
-----------------------------------------
          ptr_addr <= i.op1_num;

        when NEW_INPUT_CHECK =>
           this.op1_wrptr_rdy <= '0';
           this.op2_wrptr_rdy <= '0';
          if(ptr_addr = i.op1_num)then
            this.op1_wrptr_rdy <= '1'; 
            if(i.need_op2='0')then
              ptr_addr <= i.pc;
            else 
              ptr_addr <= i.op2_num;
            end if;
          end if;
          if(this.op1_wrptr_rdy = '1')then
            this.op1_wrptr_rdy <= '0';
            op1_wrptr_reg <= wrPtr;
          end if;
          if(ptr_addr=i.op2_num and i.need_op2='1')then
            this.op2_wrptr_rdy <= '1';
            ptr_addr <= i.pc;
          end if;
          if(this.op2_wrptr_rdy = '1')then
            this.op2_wrptr_rdy <= '0';
            op2_wrptr_reg <= wrPtr;
          end if;
          
        when FETCH_PTR =>--find the useful data and store the new read pointer
          

          --check if read from atomic directly
          if(i.is_op1_atomic='1')then
            this.queue_1_inc_finish <= '1';
          end if;
          if(i.need_op2='0' or i.is_op2_atomic='1')then
          --if(i.is_op2_atomic='1')then
            this.queue_2_inc_finish <= '1';
          end if;
          ----------------------------
          data_addr_1 <= i.op1_num & (std_logic_vector(unsigned(rdPtr_1)+unsigned(ptr_inc_1))and size_mask);
          data_addr_2 <= i.op2_num & (std_logic_vector(unsigned(rdPtr_2)+unsigned(ptr_inc_2))and size_mask);
          
          if(i.is_op1_atomic='0' and isEmpty_1='0' and this.queue_1_inc_finish='0')then--read from queue, find the proper data
            if(unsigned(rdPtr_1)=unsigned(op1_wrptr_reg))then
              isEmpty_1 <= '1';
              this.queue_1_inc_finish <= '1';
              rdPtr_1_temp <= rdPtr_1;
            else
              if(unsigned(ptr_inc_1)<2)then
                ptr_inc_1 <= std_logic_vector(unsigned(ptr_inc_1)+1);
              else
                --if unsigned(lastRd_1)<unsigned(queue_data_1.time) or lastRd_1=initial_last_value then
                if unsigned(lastRd_1)<=unsigned(queue_data_1.time) then
                  this.queue_1_inc_finish <= '1';
                  op1 <= queue_data_1;
                  rdPtr_1_temp <= std_logic_vector(unsigned(rdPtr_1)+unsigned(ptr_inc_1)-2) and size_mask;
                  ptr_inc_1 <= (others=>'0');
                else 
                  if unsigned(std_logic_vector(unsigned(rdPtr_1)+unsigned(ptr_inc_1)-1)and size_mask)=unsigned(op1_wrptr_reg) then--empty
                    this.queue_1_inc_finish <= '1';
                    isEmpty_1 <= '1';
                    rdPtr_1_temp <= std_logic_vector(unsigned(rdPtr_1)+unsigned(ptr_inc_1)-2) and size_mask;
                    ptr_inc_1 <= (others=>'0');
                  else 
                    ptr_inc_1 <= std_logic_vector(unsigned(ptr_inc_1)+1);
                  end if;
                end if;               
              end if;
            end if;
          end if;
        

          if(i.need_op2='1' and i.is_op2_atomic='0' and isEmpty_2='0' and this.queue_2_inc_finish='0')then
            if(unsigned(rdPtr_2)=unsigned(op2_wrptr_reg))then
              isEmpty_2 <= '1';
              this.queue_2_inc_finish <= '1';
              rdPtr_2_temp <= rdPtr_2;
            else
              if(unsigned(ptr_inc_2)<2)then
                ptr_inc_2 <= std_logic_vector(unsigned(ptr_inc_2)+1);
              else
                --if unsigned(lastRd_2)<unsigned(queue_data_2.time) or lastRd_2=initial_last_value then
                if unsigned(lastRd_2)<=unsigned(queue_data_2.time) then
                  this.queue_2_inc_finish <= '1';
                  op2 <= queue_data_2;
                  rdPtr_2_temp <= std_logic_vector(unsigned(rdPtr_2)+unsigned(ptr_inc_2)-2) and size_mask;
                  ptr_inc_2 <= (others=>'0');
                else 
                  if unsigned(std_logic_vector(unsigned(rdPtr_2)+unsigned(ptr_inc_2)-1)and size_mask)=unsigned(op2_wrptr_reg) then
                    this.queue_2_inc_finish <= '1';
                    isEmpty_2 <= '1';
                    rdPtr_2_temp <= std_logic_vector(unsigned(rdPtr_2)+unsigned(ptr_inc_2)-2) and size_mask;
                    ptr_inc_2 <= (others=>'0');
                  else 
                    ptr_inc_2 <= std_logic_vector(unsigned(ptr_inc_2)+1);
                  end if;
                end if;
              end if;
            end if;
          end if;

          if(this.queue_1_inc_finish='1')then--reset the flag before entering next state
            if(i.need_op2='0' or this.queue_2_inc_finish='1')then             
              ptr_inc_1 <= (others=>'0');
              ptr_inc_2 <= (others=>'0');
              debug <= '1';
              --ptr_write <= '0';
              this.queue_1_inc_finish <= '0';
              this.queue_2_inc_finish <= '0';

              if(i.command=OP_FT_UNTIL)then 
                if(unsigned(op1.time)<unsigned(op2.time))then--no need to care empty or not
                  op2.time <= op1.time;
                else
                  op1.time <= op2.time;
                end if;
              end if;
              
            end if;
          end if;

        when WAIT_NEW_RESULT =>
          ptr_addr <= i.pc;

        when UPDATE_PTR =>
          ptr_write <= '1'; 
          case i.command is 
            when OP_LOAD | OP_FT_AND | OP_FT_NOT | OP_END_SEQUENCE=> 
            --TODO
              --Pei: can we remove this?
              doSelfLoop <= '0';
              isFirstLoop <= '1';

            when OP_FT_UNTIL=>
              if(isEmpty_1='0' and isEmpty_2='0')then
                lastRd_write <= '1';
                lastRd_wrData <= std_logic_vector(unsigned(op1.time)+1) & std_logic_vector(unsigned(op2.time)+1);--whatever op1 or op2, since they are equal
                if(lastRd_wrData_mem/=std_logic_vector(unsigned(op1.time)+1) & std_logic_vector(unsigned(op2.time)+1) or isFirstLoop='1')then
                  isFirstLoop <= '0';
                  doSelfLoop <= '1';
                  lastRd_wrData_mem <= std_logic_vector(unsigned(op1.time)+1) & std_logic_vector(unsigned(op2.time)+1);
                else
                  doSelfLoop <= '0';
                  isFirstLoop <= '1';
                end if;
              end if;

            when others =>
            --Pei: why I write this code here???
            --Pei: (Answer to myself) If Boxbox or boxdot use any data for computation but with no output, we still update tau
              if(isEmpty_1='0')then
                lastRd_write <= '1';
                lastRd_wrData <= std_logic_vector(unsigned(op1.time)+1) & lastRd_2;
                if(lastRd_wrData_mem/=std_logic_vector(unsigned(op1.time)+1) & lastRd_2 or isFirstLoop='1')then
                  isFirstLoop <= '0';
                  doSelfLoop <= '1';
                  lastRd_wrData_mem <= std_logic_vector(unsigned(op1.time)+1) & lastRd_2;
                else
                  doSelfLoop <= '0';
                  isFirstLoop <= '1';
                end if;
              end if;
          end case;

          ptr_wrData <= ever_write & rdPtr_1_temp & rdPtr_2_temp & wrPtr & last_value;

          if(ptr_write='1')then
            ptr_write <= '0';
            lastRd_write <= '0';
          end if;

        when WRITE_NEW_RESULT_AND_PTR =>
          isEmpty_1 <= '0';
          isEmpty_2 <= '0';

          --data_wrData_1 <= ts_to_slv(i.new_result);
          data_wrData <= ts_to_slv(i.new_result);
          case i.command is 
            when OP_LOAD => 
              --lastRd_wrData <= i.new_result.time & lastRd_2;
              lastRd_wrData <= std_logic_vector(unsigned(i.new_result.time)+1) & lastRd_2;
              doSelfLoop <= '0'; 
              isFirstLoop <= '1';

            when OP_FT_AND =>
              lastRd_wrData <= std_logic_vector(unsigned(i.new_result.time)+1) & std_logic_vector(unsigned(i.new_result.time)+1);
              if(ptr_write='0')then
                if(lastRd_wrData_mem/=std_logic_vector(unsigned(i.new_result.time)+1) & std_logic_vector(unsigned(i.new_result.time)+1) or isFirstLoop='1')then
                  isFirstLoop <= '0';
                  doSelfLoop <= '1';
                  lastRd_wrData_mem <= std_logic_vector(unsigned(i.new_result.time)+1) & std_logic_vector(unsigned(i.new_result.time)+1);
                else
                  doSelfLoop <= '0';
                  isFirstLoop <= '1';
                end if;
              end if;

            when OP_FT_UNTIL=>
            --TODO
              lastRd_wrData <= std_logic_vector(unsigned(op1.time)+1) & std_logic_vector(unsigned(op2.time)+1);--whatever op1 or op2, since they are equal
              if(ptr_write='0')then
                if(lastRd_wrData_mem/=std_logic_vector(unsigned(op1.time)+1) & std_logic_vector(unsigned(op2.time)+1) or isFirstLoop='1')then
                  isFirstLoop <= '0';
                  doSelfLoop <= '1';
                  lastRd_wrData_mem <= std_logic_vector(unsigned(op1.time)+1) & std_logic_vector(unsigned(op2.time)+1);
                else
                  doSelfLoop <= '0';
                  isFirstLoop <= '1';
                end if;
              end if;

            when others =>
              lastRd_wrData <= std_logic_vector(unsigned(op1.time)+1) & lastRd_2;
              if(ptr_write='0')then
                if(lastRd_wrData_mem/=std_logic_vector(unsigned(op1.time)+1) & lastRd_2 or isFirstLoop='1')then
                  isFirstLoop <= '0';
                  doSelfLoop <= '1';
                  lastRd_wrData_mem <= std_logic_vector(unsigned(op1.time)+1) & lastRd_2;
                else
                  doSelfLoop <= '0';
                  isFirstLoop <= '1';
                end if;
              end if;
          end case;
          

          lastRd_write <= '1';
          --data_write_1 <= '1';
          data_write <= '1';
          ptr_write <= '1';

          -- if(i.new_result.value=last_value and lastRd_1/=initial_last_value and ever_write='1')then--need aggregation
          if(i.new_result.value=last_value and ever_write='1')then--need aggregation
            --data_addr_1 <= i.pc & (std_logic_vector(unsigned(wrPtr)-1) and size_mask);
            data_wrAddr <= i.pc & (std_logic_vector(unsigned(wrPtr)-1) and size_mask);
            ptr_wrData <= '1' & rdPtr_1_temp & rdPtr_2_temp & (wrPtr and size_mask) & i.new_result.value;
          else 
            --data_addr_1 <= i.pc & (wrPtr and size_mask);
            data_wrAddr <= i.pc & (wrPtr and size_mask);
            ptr_wrData <= '1' & rdPtr_1_temp & rdPtr_2_temp & (std_logic_vector(unsigned(wrPtr)+1) and size_mask) & i.new_result.value;
            --ptr_wrData <= rdPtr_1 & rdPtr_2 & (std_logic_vector(unsigned(wrPtr)+1) and size_mask) & i.new_result.value;
          end if;

          if(ptr_write='1')then
            doSelfLoop <= '0';
            --data_write_1 <= '0';
            data_write <= '0';
            ptr_write <= '0';
            lastRd_write <= '0';
            
          end if;

        when others =>
      end case;
    end if;
  end process;

  ever_write <= ptr_rdData(3*log2c(QUEUE_SIZE)+1);--did this observer output anything since the start
  rdPtr_1 <= ptr_rdData(3*log2c(QUEUE_SIZE) downto 2*log2c(QUEUE_SIZE)+1);
  rdPtr_2 <= ptr_rdData(2*log2c(QUEUE_SIZE) downto log2c(QUEUE_SIZE)+1);
  wrPtr <= ptr_rdData(log2c(QUEUE_SIZE) downto 1);
  last_value <= ptr_rdData(0);
  --lastRd_1 is the 
  lastRd_1 <= lastRd_rdData(2*TIMESTAMP_WIDTH-1 downto TIMESTAMP_WIDTH);
  lastRd_2 <= lastRd_rdData(TIMESTAMP_WIDTH-1 downto 0);


  queue_data_1 <= slv_to_ts(data_rdData_1);
  queue_data_2 <= slv_to_ts(data_rdData_2);

  
  size_mask(size_mask'length - 1 downto 5) <= (others=>'0');
  size_mask(4 downto 0) <= (others=>'1');
  o.state <= this.state;
  o.isEmpty_1 <= isEmpty_1;
  o.isEmpty_2 <= isEmpty_2;
  o.op1 <= op1;
  o.op2 <= op2;
  o.ptr_write <= ptr_write;
  o.doSelfLoop <= doSelfLoop;

end architecture;
