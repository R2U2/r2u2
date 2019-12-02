----------------------------------------------------------------------------------
-- Company: 
-- Engineer: 
-- 
-- Create Date: 11/21/2017 02:01:56 PM
-- Design Name: 
-- Module Name: R2U2 - Behavioral
-- Project Name: 
-- Target Devices: 
-- Tool Versions: 
-- Description: 
-- 
-- Dependencies: 
-- 
-- Revision:
-- Revision 0.01 - File Created
-- Additional Comments:
-- 
----------------------------------------------------------------------------------


library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use ieee.numeric_std.all;
use ieee.std_logic_unsigned.all;
use work.ft_mu_monitor_pkg.all;
use work.mu_monitor_pkg.all;
use work.log_input_pkg.all;
use work.R2U2_pkg.all;
-- Uncomment the following library declaration if using
-- arithmetic functions with Signed or Unsigned values
--use IEEE.NUMERIC_STD.ALL;

-- Uncomment the following library declaration if instantiating
-- any Xilinx leaf cells in this code.
--library UNISIM;
--use UNISIM.VComponents.all;

entity R2U2 is
    Port ( 
        clk : in std_logic;
        rst : in std_logic;
        ConfigSTATE : in config_type;
        input_rdy : in std_logic;
        setup_addr : in std_logic_vector(SETUP_ADDR_WIDTH-1 downto 0);
        setup_data : in std_logic_vector(SETUP_DATA_WIDTH-1 downto 0);
        data : in std_logic_vector(LOG_DATA_WIDTH-1 downto 0);
        debug : out debug_t;
        res_verdict: out std_logic;
        res_timestamp : out std_logic_vector(TIMESTAMP_WIDTH-1 downto 0);
        res_rdy : out std_logic;
        res_exist : out std_logic
        );
end R2U2;

architecture Behavioral of R2U2 is


component at_checkers is
    port(
        clk          : in std_logic;
        rst_n        : in std_logic;
        config_addr  : in std_logic_vector(11-1 downto 0);
        config_data  : in std_logic_vector(32-1 downto 0);
        config_write : in std_logic;
        sample_clk   : in std_logic;
        data         : in std_logic_vector(LOG_DATA_WIDTH-1 downto 0);
        atomics      : out std_logic_vector(ATOMICS_WIDTH-1 downto 0)
    );
end component;


signal atomics : std_logic_vector(ATOMICS_WIDTH-1 downto 0);
signal atmoics_reversed : std_logic_vector(ATOMICS_WIDTH-1 downto 0);
signal programming_memory_addr : std_logic_vector(MEMBUS_ADDR_WIDTH-1 downto 0);
signal programming_memory_data : std_logic_vector(MEMBUS_DATA_WIDTH-1 downto 0);

type state_type is (idel, config_ac, config_fm_imem, config_fm_int, run, send_res);
signal ps : state_type;
signal ns : state_type;

signal config_write : std_logic;
signal imem_wr : std_logic;
signal int_wr : std_logic;
signal config_addr : std_logic_vector(11-1 downto 0);
signal config_data : std_logic_vector(32-1 downto 0);



signal signal_out : std_logic;
signal trigger : std_logic;
signal rtc_timestamp : std_logic_vector(TIMESTAMP_WIDTH - 1 downto 0);
signal hold_rtc_timestamp : std_logic_vector(TIMESTAMP_WIDTH - 1 downto 0); 
constant LATENCY : integer := 7; -- associate with how long the at_checkers can produce output
type signal_dly_type is array (0 to LATENCY-1) of std_logic;
signal signal_dly : signal_dly_type;
signal signal_in : std_logic;
signal debug_sig : debug_t;

begin

state_update : process(clk, rst)
begin
    if(clk = '1' and clk' event)then
        if(rst = '0')then
            ps <= idel;
        else
            ps <= ns;
        end if;
    end if;
end process;


comb_state_update : process(rst, ps, ConfigSTATE)
begin
    if(rst='0')then
        ns <= idel;
    else
        ns <= ps;
        case ps is
            when idel =>
                if(ConfigSTATE=config_ac)then
                    ns <= config_ac;
                end if;
            when config_ac => 
                if(ConfigSTATE=config_fm_imem)then
                    ns <= config_fm_imem;
                end if;
            when config_fm_imem =>
                if(ConfigSTATE=config_fm_int)then
                    ns <= config_fm_int;
                end if;
            when config_fm_int =>
                if(ConfigSTATE=config_log_data)then
                    ns <= run;
                end if;
            when others=>
        end case;
    end if;
end process;


RTC : process(rst, clk)
begin
    if(clk = '1' and clk' event)then
        if(rst='0')then
            rtc_timestamp <= (others => '0');
            hold_rtc_timestamp <= (others=>'0');
        else            
            if(trigger='1')then
                hold_rtc_timestamp <= rtc_timestamp;
                rtc_timestamp <= std_logic_vector(unsigned(rtc_timestamp)+1);
            end if;
        end if;
    end if;


end process;


reverse_bit : process(clk, rst)
begin
    if(clk = '1' and clk' event)then
        if(rst = '0')then
            atmoics_reversed <= (others =>'0');
        else
            for I in 0 to atmoics_reversed'length-1 loop
            --for I in 0 to 1 loop
                atmoics_reversed(I) <= atomics(atmoics_reversed'length-I-1);
            end loop;
        end if;
    end if;
end process;


at_chekcer_rdy: process(clk, rst)
begin
    if(clk' event and clk = '1')then
        if(rst = '0')then
            for i in 0 to LATENCY-1 loop
                signal_dly(i) <= '0';
            end loop;
        else    
            signal_dly(0) <= signal_in; 
            for i in 0 to LATENCY-2 loop
                signal_dly(i+1) <= signal_dly(i);
            end loop;   
        end if;
    end if;
end process;
signal_out <= signal_dly(LATENCY-1);
trigger <= signal_out;

signal_in <= input_rdy when ps = run else '0';






--config_write <= input_rdy when (ps=config_ac or ps = run) else '0';
config_write <= input_rdy when ps=config_ac else '0';
imem_wr <= input_rdy when ps = config_fm_imem else '0';
int_wr <= input_rdy when ps = config_fm_int else '0';

programming_memory_addr <= setup_addr(MEMBUS_ADDR_WIDTH-1 downto 0) when (ps=config_fm_imem or ps=config_fm_int) else (others=>'0');
config_addr <= setup_addr(11-1 downto 0) when (ps=config_ac) else (others=>'0');

programming_memory_data <= setup_data(MEMBUS_DATA_WIDTH-1 downto 0) when (ps=config_fm_imem or ps=config_fm_int) else (others=>'0');
config_data <= setup_data(32-1 downto 0) when (ps=config_ac) else (others=>'0');

res_verdict <= debug_sig.new_result.value;
res_timestamp <= debug_sig.new_result.time;
res_rdy <= debug_sig.new_result_rdy;
res_exist <= debug_sig.have_new_result;
debug <= debug_sig;

at_checkers_unit : at_checkers
    port map(
        clk          => clk,
        rst_n        => rst,
        config_addr  => config_addr,
        config_data  => config_data,
        config_write => config_write,
        sample_clk   => clk,--use clk first
        data         => data,
        atomics      => atomics
        );


ft_mu_monotor_unit : ft_mu_monitor
    port map
    (
      clk                     => clk,
      reset_n                 => rst,
      --atomics                 => atmoics_reversed,
      atomics                 => atomics,
      timestamp               => hold_rtc_timestamp,
      en                      => '1',
      trigger                 => trigger,
      program_addr            => programming_memory_addr,
      program_data            => programming_memory_data,
      program_imem            => imem_wr, --instruction mem write signal
      program_interval_memory => int_wr, --interval mem write signal
      violated                => open,
      violated_valid          => open,
      pt_data_memory_addr     => open,
      pt_data_memory_data     => '0',
      sync_out                => open,
      finish                  => open,
      data_memory_async_data  => open,
      data_memory_async_empty => open,
      data_memory_sync_data   => open,
      data_memory_addr        => (others => '0'),
      
      --Pei: signal for simulation to replace spy function 
      this_new_result         => open,
      this_sync_out_data_time => open,
      --this_sync_out_data_value => result_value_spy

      --Pei: signal for writing output
      debug => debug_sig
      );
end Behavioral;
