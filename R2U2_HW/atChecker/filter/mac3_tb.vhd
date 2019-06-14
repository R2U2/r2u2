-------------------------------------------------------------------------------
-- Title      : Testbench for design "mac3"
-- Project    : 
-------------------------------------------------------------------------------
-- File       : mac3_tb.vhd
-- Author     :   <Jo@JGWIN8-MOBILE>
-- Company    : 
-- Created    : 2014-03-07
-- Last update: 2014-03-07
-- Platform   : 
-- Standard   : VHDL'93/02
-------------------------------------------------------------------------------
-- Description: 
-------------------------------------------------------------------------------
-- Copyright (c) 2014 
-------------------------------------------------------------------------------
-- Revisions  :
-- Date        Version  Author  Description
-- 2014-03-07  1.0      Jo      Created
-------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

-------------------------------------------------------------------------------

entity mac3_tb is

end entity mac3_tb;

-------------------------------------------------------------------------------

architecture sim of mac3_tb is

  -- component generics
  constant DATA_WIDTH : integer := 16;

  -- component ports
  signal s_clk        : std_logic := '0';
  signal s_rst_n      : std_logic := '0';
  signal s_sample_clk : std_logic := '0';
  signal s_data_in_1  : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal s_data_in_2  : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal s_data_in_3  : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal s_data_out   : std_logic_vector((2*DATA_WIDTH)+2-1 downto 0);

begin  -- architecture sim

  -- component instantiation
  DUT : entity work.mac3
    generic map (
      DATA_WIDTH => DATA_WIDTH)
    port map (
      clk        => s_clk,
      rst_n      => s_rst_n,
      sample_clk => s_sample_clk,
      data_in_1  => s_data_in_1,
      data_in_2  => s_data_in_2,
      data_in_3  => s_data_in_3,
      data_out   => s_data_out);

  -- clock generation
  s_clk        <= not s_clk        after 10 ns;
  s_sample_clk <= not s_sample_clk after 100 ns;

  -- reset generation
  s_rst_n <= '1' after 50 ns;

  -- waveform generation
  WaveGen_Proc : process
    variable v_i : integer := 0;
  begin
    report "testcase FAILED" severity warning;
    -- insert signal assignments herei
    if (s_rst_n = '1') then
      v_i         := v_i + 1;
      s_data_in_1 <= std_logic_vector(to_signed((1+v_i), DATA_WIDTH));
      s_data_in_2 <= std_logic_vector(to_signed((56+v_i), DATA_WIDTH));
      s_data_in_3 <= std_logic_vector(to_signed((111+v_i), DATA_WIDTH));
      wait until s_sample_clk = '1';
    else
      wait for 100 ns;
    end if;

  end process WaveGen_Proc;



end architecture sim;

-------------------------------------------------------------------------------

configuration mac3_tb_sim_cfg of mac3_tb is
  for sim
  end for;
end mac3_tb_sim_cfg;

-------------------------------------------------------------------------------
