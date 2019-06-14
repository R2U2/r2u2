----------------------------------------------------------------------------------
-- Company: 
-- Engineer: 
-- 
-- Create Date:    11/23/2017 
-- Design Name: 
-- Module Name:    echo - Behavioral 
-- Project Name: 
-- Target Devices: 
-- Tool versions: 
-- Description: Echo data recived from the UART back to the PC
--
-- Dependencies: 
--
-- Revision: 
-- Revision 0.01 - File Created
-- Additional Comments: 
-- ALL the UART data should send from lower BYTE to high BYTE
----------------------------------------------------------------------------------

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.NUMERIC_STD.ALL;
use work.log_input_pkg.all;
use work.mu_monitor_pkg.all;
use work.ft_mu_monitor_pkg.all;
use work.ram_pkg.all;
use work.math_pkg.all;
use work.R2U2_pkg.all;
-- Uncomment the following library declaration if using
-- arithmetic functions with Signed or Unsigned values
--use IEEE.NUMERIC_STD.ALL;

-- Uncomment the following library declaration if instantiating
-- any Xilinx primitives in this code.
--library UNISIM;
--use UNISIM.VComponents.all;

entity echo is
    Port ( 
            clk       : in  STD_LOGIC;
            reset     : in STD_LOGIC;
            new_data  : in  STD_LOGIC; -- Indicate a new byte has been captured from UART
            data_in   : in  STD_LOGIC_VECTOR (7 downto 0);
            TX_busy_n : in  STD_LOGIC;
            send_data : out  STD_LOGIC; -- Request UART to tranmite data_out
            data_out  : out  STD_LOGIC_VECTOR (7 downto 0);
            LD0 : out std_logic;
            LD1 : out std_logic
            );
end echo;

architecture Behavioral of echo is

-- Components
  -- None
  
-- signals
signal rdy_send_data_reg : std_logic; -- Indicate there is that is ready to be sent
signal send_data_reg  : std_logic; -- Tell UART to send a byte of data
signal data_out_reg   : std_logic_vector(7 downto 0); -- Temp storage for new data


signal rst : std_logic;
type state_type is (idel, collect_general_info, import_ac, import_imem, import_intMem, receive_log_data, 
    check_send_res, process_pc, process_verdict, process_timestamp, wait_send_res, send_res);
signal ps : state_type;
signal ns : state_type;
signal prepare_rdy : std_logic;
signal data_cnt : std_logic_vector(7 downto 0);
signal inner_data_cnt : std_logic_vector(7 downto 0);
signal ConfigSTATE : config_type;
signal is_wr_data : std_logic;
signal combine_addr : std_logic_vector(SETUP_ADDR_WIDTH_extend-1 downto 0);
signal combine_data : std_logic_vector(SETUP_DATA_WIDTH_extend-1 downto 0);
signal switch_state : std_logic;
signal log_data : std_logic_vector(DATA_BYTE_WIDTH_extend-1 downto 0);

type config_info_type is record
    num_of_at_checker_add_to_config    : std_logic_vector(7 downto 0);
    num_of_imem_to_config : std_logic_vector(7 downto 0);
    num_of_int_to_config : std_logic_vector(7 downto 0);
end record;

signal config_info : config_info_type;
signal config_info_reset : config_info_type := (
    num_of_at_checker_add_to_config  => (others=>'0'),
    num_of_imem_to_config => (others=>'0'),
    num_of_int_to_config => (others=>'0')
    );

signal res_verdict : std_logic;
signal res_timestamp : std_logic_vector(TIMESTAMP_WIDTH - 1 downto 0);
signal res_rdy : std_logic;
signal res_exist : std_logic;
signal res_timestamp_extend : std_logic_vector(TIMESTAMP_WIDTH_extend-1 downto 0);
signal finish_send : std_logic;
signal send_byte_cnt : std_logic_vector(7 downto 0);
signal dly_cnt : std_logic_vector(3 downto 0);
signal finish_receive : std_logic;
signal debug : debug_t;
signal res_cnt : std_logic_vector(7 downto 0);
signal finish_send_hold : std_logic;
signal send_next : std_logic;

signal addr : std_logic_vector(log2c(3*NUMBER_OF_QUEUES)-1 downto 0);
signal wrData : std_logic_vector(TIMESTAMP_WIDTH_extend-1 downto 0);
signal write : std_logic;
signal rdData : std_logic_vector(TIMESTAMP_WIDTH_extend-1 downto 0);



signal LD0_signal : std_logic;
signal LD1_signal : std_logic;

begin

LD0 <= LD0_signal;
LD1 <= LD1_signal;

-- Assign outputs
send_data <= send_data_reg;
data_out  <= data_out_reg;


state_update : process(clk, reset)
begin
    if(clk = '1' and clk' event)then
        if(reset = '1')then
            ps <= idel;
        else
            ps <= ns;
        end if;
    end if;
end process;


comb_state_update : process(reset, ps, switch_state, finish_send, send_next, finish_receive,
    debug.have_new_result_intermediate,finish_send_hold)
begin
    if(reset='1')then
        ns <= idel;
    else
        ns <= ps;
        case ps is
            when idel =>
                ns <= collect_general_info;
            when collect_general_info => 
                if(switch_state='1')then
                    ns <= import_ac;
                end if;
            when import_ac =>
                if(switch_state='1')then
                    ns <= import_imem;
                end if;
            when import_imem =>
                if(switch_state='1')then
                    ns <= import_intMem;
                end if;
            when import_intMem =>
                if(switch_state='1')then
                    ns <= receive_log_data;
                end if;
            when receive_log_data =>
                if(finish_receive='1')then
                    ns <= check_send_res;
                end if;

            when check_send_res =>
                if(debug.have_new_result_intermediate = '1')then
                    ns <= process_pc;
                end if;
                if(finish_send_hold = '1')then--CAUTION: sm may miss this signal
                    ns <= wait_send_res;
                end if;

            when process_pc =>
                ns <= process_verdict;
            when process_verdict =>
                ns <= process_timestamp;
            when process_timestamp =>
                ns <= check_send_res;
            
            when wait_send_res =>
                if(finish_send='1')then
                    ns <= receive_log_data;
                end if;
                if(send_next='1')then
                    ns <= send_res;
                end if;

            when send_res =>
                --if(switch_state='1')then
                    ns <= wait_send_res;
                --end if;




            --when send_res_verdict =>
            --    if(switch_state ='1')then
            --        ns <= send_res_timestmap;
            --    end if;
            --when wait_send_res_timestmap =>
            --    if(rdy_send_data_reg='0')then
            --        ns <= send_res_timestmap;
            --    end if;
            --when send_res_timestmap =>
            --    if(finish_send='1')then
            --        ns <= receive_log_data;
            --    elsif(switch_state='1')then
            --        ns <= wait_send_res_timestmap;
            --    end if;
            when others=>
        end case;
    end if;
end process;

--combine the data from receiving
combine_data_process : process(clk,reset)
begin
    if(clk'event and clk='1')then
        if(reset = '1')then
            data_cnt <= (others=>'0');
            inner_data_cnt <= (others=>'0');
            is_wr_data <= '0';
            switch_state <= '0';
            combine_addr <= (others=>'0');
            combine_data <= (others=>'0');
            log_data <= (others=>'0');
            prepare_rdy <= '0';
            config_info <= config_info_reset;
            dly_cnt <= (others=>'0');
            finish_receive <= '0';
            addr <= (others=>'0');
            wrData <= (others=>'0');
            rdy_send_data_reg <= '0';
            send_data_reg     <= '0';
            data_out_reg      <= (others => '0');     
            finish_send <= '0';
            res_cnt <= (others=>'0');
            --send_byte_cnt <= (others=>'0');
            finish_send_hold <= '0';
            send_next <= '0';
            LD0_signal <= '0';
            LD1_signal <= '0';
        else
            send_data_reg <= '0';
            finish_send <= '0';
            finish_receive <= '0';
            write <= '0';
            send_next <= '0';
            if(debug.finish='1')then
                finish_send_hold <= '1';
                addr <= (others=>'0');
            end if;

            if(write='1')then
                addr <= std_logic_vector(unsigned(addr)+1);
            end if;

            if(switch_state = '1')then
                switch_state <= '0';
            end if;
            if(prepare_rdy = '1')then
                prepare_rdy <= '0';
                if(ps=import_imem or ps=import_intMem)then
                    combine_addr <= std_logic_vector(unsigned(combine_addr)+1);
                end if;
            end if;
            if(switch_state='0')then
                case ps is 

                    when collect_general_info =>
                        LD0_signal <= '1';
                        if (unsigned(data_cnt) = 3) then
                            data_cnt <= (others=>'0');
                            switch_state <= '1';
                        end if;
                    when import_ac =>
                        LD1_signal <= '1';
                        if(unsigned(data_cnt)=unsigned(config_info.num_of_at_checker_add_to_config))then
                            data_cnt <= (others=>'0');                        
                            switch_state <= '1';
                            combine_addr <= (others => '0');-------------
                            
                        end if;
                    when import_imem =>
                        
                        if(unsigned(data_cnt)=unsigned(config_info.num_of_imem_to_config))then
                            data_cnt <= (others=>'0');
                            switch_state <= '1';
                            combine_addr <= (others => '0');-------------
                        end if;
                    when import_intMem =>
                        if(unsigned(data_cnt)=unsigned(config_info.num_of_int_to_config))then
                            data_cnt <= (others=>'0');
                            switch_state <= '1';
                            combine_addr <= (others => '0');-------------
                        end if;
                    when receive_log_data =>
                        if(unsigned(data_cnt)=1)then
                            data_cnt <= (others=>'0');
                            finish_receive <= '1';
                            
                        end if;


                    when others =>

                end case;
            end if;





            if(new_data='1')then
            --------------------receive data
                case ps is
                    when collect_general_info =>
                        data_cnt <= std_logic_vector(unsigned(data_cnt)+1);
                        if (unsigned(data_cnt) = 0) then
                            config_info.num_of_at_checker_add_to_config <= data_in;
                        elsif (unsigned(data_cnt) = 1) then
                            config_info.num_of_imem_to_config <= data_in;
                        elsif (unsigned(data_cnt) = 2) then
                            config_info.num_of_int_to_config <= data_in;        
                        end if;
                    when import_ac =>
                        inner_data_cnt <= std_logic_vector(unsigned(inner_data_cnt)+1);
                        if(is_wr_data = '0')then
                            for I in 0 to CONFIG_ADDR_BYTE-1 loop
                                if(unsigned(inner_data_cnt)=I)then
                                    combine_addr( (I+1)*8-1 downto I*8 ) <= data_in;
                                end if;                                
                            end loop;
                            if(unsigned(inner_data_cnt)=CONFIG_ADDR_BYTE-1)then
                                is_wr_data <= '1';
                                inner_data_cnt <= (others=>'0');
                            end if;
                        else
                            for I in 0 to CONFIG_DATA_BYTE-1 loop
                                if(unsigned(inner_data_cnt)=I)then
                                    combine_data( (I+1)*8-1 downto I*8 ) <= data_in;
                                end if;                                
                            end loop;
                            if(unsigned(inner_data_cnt)=CONFIG_DATA_BYTE-1)then
                                is_wr_data <= '0';
                                prepare_rdy <= '1';
                                inner_data_cnt <= (others=>'0');
                                data_cnt <= std_logic_vector(unsigned(data_cnt)+1);
                            end if;
                        end if;

                    when import_imem | import_intMem =>
                        inner_data_cnt <= std_logic_vector(unsigned(inner_data_cnt)+1);
                        for I in 0 to CONFIG_DATA_BYTE-1 loop
                                if(unsigned(inner_data_cnt)=I)then
                                    combine_data( (I+1)*8-1 downto I*8 ) <= data_in;
                                end if;                                
                        end loop;
                        if(unsigned(inner_data_cnt)=CONFIG_DATA_BYTE-1)then
                            --is_wr_data <= '0';
                            prepare_rdy <= '1';
                            inner_data_cnt <= (others=>'0');
                            data_cnt <= std_logic_vector(unsigned(data_cnt)+1);
                        end if;

                    when receive_log_data =>
                        finish_send_hold <= '0';
                        inner_data_cnt <= std_logic_vector(unsigned(inner_data_cnt)+1);
                        for I in 0 to DATA_BYTE-1 loop
                            if(unsigned(inner_data_cnt)=I)then
                                log_data( (I+1)*8-1 downto I*8 ) <= data_in;
                            end if;                                
                        end loop;
                        if(unsigned(inner_data_cnt)=DATA_BYTE-1)then
                            prepare_rdy <= '1';
                            inner_data_cnt <= (others=>'0');
                            data_cnt <= std_logic_vector(unsigned(data_cnt)+1);
                        end if;

                    when others =>
                end case;
                --rdy_send_data_reg <= '1';
                --data_out_reg  <= data_in;
            else
            --------------------send data
                case ps is

                    when process_pc =>
                        res_cnt <= std_logic_vector(unsigned(res_cnt)+1);
                        write <= '1';
                        wrData(log2c(ROM_LEN) - 1 downto 0) <= debug.pc_debug;
                        wrData(wrData'length-1 downto log2c(ROM_LEN)) <= (others=>'0');
                    when process_verdict =>
                        res_cnt <= std_logic_vector(unsigned(res_cnt)+1);
                        write <= '1';
                        wrData(0) <= debug.new_result.value;
                        wrData(wrData'length-1 downto 1) <= (others=>'0');
                    when process_timestamp =>
                        res_cnt <= std_logic_vector(unsigned(res_cnt)+1);
                        write <= '1';
                        wrData(TIMESTAMP_WIDTH_extend-1 downto 0) <= debug.new_result.time;

                    when wait_send_res=>
                        if(rdy_send_data_reg='0')then--transmit complete
                            if(unsigned(data_cnt)=unsigned(res_cnt))then
                                finish_send <= '1';
                                res_cnt <= (others=>'0');
                                data_cnt <= (others=>'0');
                                addr <= (others=>'0');
                            else
                                send_next <= '1';
                            end if;
                        end if;
                    
                    when check_send_res =>
                        if(finish_send_hold='1')then
                            addr <= (others=>'0');
                        end if;

                    when send_res =>
                        rdy_send_data_reg <= '1';
                        switch_state <= '1';
                        inner_data_cnt <= std_logic_vector(unsigned(inner_data_cnt)+1);
                        for I in 0 to TIMESTAMP_BYTE-1 loop
                            if(unsigned(inner_data_cnt)=I)then
                                data_out_reg <= rdData( (I+1)*8-1 downto I*8 );
                            end if;                                
                        end loop;
                        if(unsigned(inner_data_cnt)=TIMESTAMP_BYTE-1)then
                            addr <= std_logic_vector(unsigned(addr)+1);
                            inner_data_cnt <= (others=>'0');
                            data_cnt <= std_logic_vector(unsigned(data_cnt)+1);
                            addr <= std_logic_vector(unsigned(addr)+1);
                        end if;



                    --when send_res_verdict =>
                    --    if(rdy_send_data_reg='0')then
                    --        rdy_send_data_reg <= '1';  -- keep high until the UART is ready for us
                    --                                    -- to transmit a byte
                    --        data_out_reg <= (others=>'0');
                    --        data_out_reg(0) <= res_verdict;
                            
                    --    end if;
                    --when wait_send_res_timestmap =>
                    --    if(rdy_send_data_reg='0')then
                    --        send_byte_cnt <= std_logic_vector(unsigned(send_byte_cnt)+1);
                    --    end if;
                    --when send_res_timestmap =>
                    --    if(unsigned(send_byte_cnt)=TIMESTAMP_BYTE)then
                    --        finish_send <= '1';
                    --        send_byte_cnt <= (others=>'0');
                    --    else
                    --        if(rdy_send_data_reg='0')then
                    --            rdy_send_data_reg <= '1';  -- keep high until the UART is ready for us
                    --                                        -- to transmit a byte
                    --            for I in 0 to TIMESTAMP_BYTE-1 loop
                    --                if(unsigned(send_byte_cnt)=I)then
                    --                    data_out_reg <= res_timestamp_extend( (I+1)*8-1 downto I*8 );
                    --                end if;                                
                    --            end loop;
                    --        end if;
                    --    end if;
                    when others =>
                end case;

                if(rdy_send_data_reg = '1') then        
                    if(TX_busy_n = '1') then -- Check if UART is busy transmitting already
                        rdy_send_data_reg <= '0'; -- reset this signal
                        send_data_reg <= '1';     -- tell UART to transmit a byte
                        switch_state <= '1';
                    end if;
                end if;

            end if;    
        end if;
    end if;
end process;


rst <= not reset;

res_timestamp_extend(TIMESTAMP_WIDTH-1 downto 0) <= res_timestamp;
res_timestamp_extend(TIMESTAMP_WIDTH_extend -1 downto TIMESTAMP_WIDTH) <= (others=>'0');

ConfigSTATE <= config_ac when ps = import_ac 
    else config_fm_imem when ps = import_imem
    else config_fm_int when ps = import_intMem
    else config_log_data when ps = receive_log_data
    else idel;


    r2u2_main : R2U2
    port map( 
        clk => clk,
        rst => rst,
        ConfigSTATE => ConfigSTATE,
        input_rdy => prepare_rdy,
        setup_addr => combine_addr(SETUP_ADDR_WIDTH-1 downto 0),
        setup_data => combine_data(SETUP_DATA_WIDTH-1 downto 0),
        data => log_data(LOG_DATA_WIDTH-1 downto 0),
        debug => debug,
        res_verdict => res_verdict,
        res_timestamp => res_timestamp,
        res_rdy => res_rdy,
        res_exist => res_exist
        );



    output_ram : sp_ram
    generic map(
      ADDR_WIDTH => log2c(3*NUMBER_OF_QUEUES),
      DATA_WIDTH => TIMESTAMP_WIDTH_extend
      )
    port map(
      clk    => clk,
      addr   => addr,
      wrData => wrData,
      write  => write,
      rdData => rdData
      );

end Behavioral;
