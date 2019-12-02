-------------------------------------------------------------------------------
-- Title      : Testbench for design "divider_fsm"
-- Project    : 
-------------------------------------------------------------------------------
-- File       : divider_fsm_tb.vhd
-- Author     :   <xiaot@ponyo>
-- Company    : 
-- Created    : 2012-06-29
-- Last update: 2012-06-29
-- Platform   : 
-- Standard   : VHDL'87
-------------------------------------------------------------------------------
-- Description: 
-------------------------------------------------------------------------------
-- Copyright (c) 2012 
-------------------------------------------------------------------------------
-- Revisions  :
-- Date        Version  Author  Description
-- 2012-06-29  1.0      xiaot	Created
-------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use work.testbench_util_pkg.all;

-------------------------------------------------------------------------------

entity divider_fsm_tb is

end divider_fsm_tb;

-------------------------------------------------------------------------------

architecture divider_fsm_tb of divider_fsm_tb is

  component divider_fsm
    generic (
      NUM_OF_BITS : integer;
      TICK        : integer);
    port (
      clk       : in  std_logic;
      reset_n   : in  std_logic;
      run       : in  std_logic;
      dividend  : in  std_logic_vector((NUM_OF_BITS - 1) downto 0);
      enable    : in  std_logic;
      divisor   : in  std_logic_vector((NUM_OF_BITS - 1) downto 0);
      quotient  : out std_logic_vector((NUM_OF_BITS - 1) downto 0);
      remainder : out std_logic_vector((NUM_OF_BITS - 1) downto 0);
      fin       : out std_logic);
  end component;

  -- component generics
  constant NUM_OF_BITS : integer := 10;
  constant TICK        : integer := 0;

  -- component ports
  signal s_clk       : std_logic := '0';
  signal s_reset_n   : std_logic := '0';
  signal s_run       : std_logic := '0';
  signal s_enable    : std_logic := '0';
  signal s_dividend  : std_logic_vector((NUM_OF_BITS - 1) downto 0);
  signal s_divisor   : std_logic_vector((NUM_OF_BITS - 1) downto 0);
  signal s_quotient  : std_logic_vector((NUM_OF_BITS - 1) downto 0);
  signal s_remainder : std_logic_vector((NUM_OF_BITS - 1) downto 0);
  signal s_fin       : std_logic;


begin  -- divider_fsm_tb

  -- component instantiation
  DUT: divider_fsm
    generic map (
      NUM_OF_BITS => NUM_OF_BITS,
      TICK        => TICK)
    port map (
      clk       => s_clk,
      reset_n   => s_reset_n,
      run       => s_run,
      dividend  => s_dividend,
      enable    => s_enable,
      divisor   => s_divisor,
      quotient  => s_quotient,
      remainder => s_remainder,
      fin       => s_fin);

  -- clock generation
  s_clk <= not s_clk after 10 ps;
  s_reset_n <= '1' after 50 ns;

  -- waveform generation
  WaveGen_Proc: process
  begin
    -- insert signal assignments here
     wait until s_clk = '1';
     s_dividend <= conv_std_logic_vector(100, NUM_OF_BITS);
     s_divisor  <= conv_std_logic_vector(10, NUM_OF_BITS);
     wait for 100 ns;
     s_enable <= '1';
     wait for 10 ns;
     s_run <= '1';
     wait_cycle(s_clk,1);
     s_run <= '0';
     wait until s_fin = '1';
  end process WaveGen_Proc;

end divider_fsm_tb;

-------------------------------------------------------------------------------
configuration divider_fsm_tb_divider_fsm_tb_cfg of divider_fsm_tb is
  for divider_fsm_tb
  end for;
end divider_fsm_tb_divider_fsm_tb_cfg;
-------------------------------------------------------------------------------
