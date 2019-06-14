-------------------------------------------------------------------------------
-- Project    : CevTes RVU (Runtime Verification Unit)
-------------------------------------------------------------------------------
-- File       : fifo.vhd
-- Author     : Daniel Schachinger
-- Copyright  : 2011, Thomas Reinbacher (treinbacher@ecs.tuwien.ac.at)
--              Vienna University of Technology, ECS Group
-------------------------------------------------------------------------------
-- Description: A general purpose FIFO implemenetation
-------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pkg.all;
use work.fifo_pkg.all;
use work.ram_pkg.all;

entity fifo is
  generic
    (
      MIN_DEPTH  : integer;
      DATA_WIDTH : integer
      );
  port
    (
      clk      : in  std_logic;
      res_n    : in  std_logic;
      data_out : out std_logic_vector(DATA_WIDTH - 1 downto 0);
      data_in  : in  std_logic_vector(DATA_WIDTH - 1 downto 0);
      ctrl_o   : out fifo_ctrl_out_type;
      ctrl_i   : in  fifo_ctrl_in_type
      );
end entity fifo;

architecture fifo_beh of fifo is
  
  signal read_address, read_address_next   : std_logic_vector(log2c(MIN_DEPTH) - 1 downto 0);
  signal write_address, write_address_next : std_logic_vector(log2c(MIN_DEPTH) - 1 downto 0);
  signal full_int, full_next               : std_logic;
  signal empty_int, empty_next             : std_logic;
  signal wr_int, rd_int                    : std_logic;
begin
  memory_inst : ram
    generic map
    (
      ADDR_WIDTH => log2c(MIN_DEPTH),
      DATA_WIDTH => DATA_WIDTH
      )
    port map
    (
      clk   => clk,
      raddr => read_address,
      rdata => data_out,
      rd    => rd_int,
      waddr => write_address,
      wdata => data_in,
      wr    => wr_int
      ); 

  sync : process(clk, res_n)
  begin
    if res_n = '0' then
      read_address  <= (others => '0');
      write_address <= (others => '0');
      full_int      <= '0';
      empty_int     <= '1';
    elsif rising_edge(clk) then
      read_address  <= read_address_next;
      write_address <= write_address_next;
      full_int      <= full_next;
      empty_int     <= empty_next;
    end if;
  end process sync;

  exec : process(write_address, read_address, full_int, empty_int, ctrl_i)
  begin
    write_address_next <= write_address;
    read_address_next  <= read_address;
    full_next          <= full_int;
    empty_next         <= empty_int;
    wr_int             <= '0';
    rd_int             <= '0';

    if ctrl_i.wr = '1' and full_int = '0' then
      wr_int             <= '1';        -- only write, if fifo is not full
      write_address_next <= std_logic_vector(unsigned(write_address) + 1);
    end if;

    if ctrl_i.rd = '1' and empty_int = '0' then
      rd_int            <= '1';         -- only read, if fifo is not empty
      read_address_next <= std_logic_vector(unsigned(read_address) + 1);
    end if;

    -- if memory is empty after current read operation
    if ctrl_i.rd = '1' then
      full_next <= '0';
      if write_address = std_logic_vector(unsigned(read_address) + 1) then
        empty_next <= '1';
      end if;
    end if;

    -- if memory is full after current write operation
    if ctrl_i.wr = '1' then
      empty_next <= '0';
      if read_address = std_logic_vector(unsigned(write_address) + 1) then
        full_next <= '1';
      end if;
    end if;
  end process exec;

  ctrl_o.full  <= full_int;
  ctrl_o.empty <= empty_int;
end fifo_beh;
