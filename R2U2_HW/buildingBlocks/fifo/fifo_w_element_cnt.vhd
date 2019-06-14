-------------------------------------------------------------------------------
-- Project    : CevTes RVU (Runtime Verification Unit)
-------------------------------------------------------------------------------
-- File       : fifo_w_element_cnt.vhd
-- Author     : Thomas Reinbacher
-- Copyright  : 2011, Thomas Reinbacher (treinbacher@ecs.tuwien.ac.at)
--              Vienna University of Technology, ECS Group
-------------------------------------------------------------------------------
-- Description: A general purpose FIFO implementation; 
--              provides the number of stored elements at the output
-------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pkg.all;
use work.fifo_pkg.all;
use work.ram_pkg.all;

entity fifo_w_element_cnt is
  generic
    (
      MIN_DEPTH      : integer;
      DATA_WIDTH     : integer
      );
  port
    (
      clk         : in  std_logic;
      res_n       : in  std_logic;
      data_out    : out std_logic_vector(DATA_WIDTH - 1 downto 0);
      data_in     : in  std_logic_vector(DATA_WIDTH - 1 downto 0);
      elements    : out std_logic_vector(log2c(MIN_DEPTH)  downto 0);
      ctrl_o      : out fifo_ctrl_out_type;
      ctrl_i      : in  fifo_ctrl_in_type
      );
end entity fifo_w_element_cnt;

architecture fifo_beh of fifo_w_element_cnt is
  
  signal read_address, read_address_next   : std_logic_vector(log2c(MIN_DEPTH) - 1 downto 0);
  signal write_address, write_address_next : std_logic_vector(log2c(MIN_DEPTH) - 1 downto 0);
  signal elements_int, elements_next       : std_logic_vector(log2c(MIN_DEPTH) downto 0);
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
      elements_int  <= (others => '0');
      full_int      <= '0';
      empty_int     <= '1';
    elsif rising_edge(clk) then
      read_address  <= read_address_next;
      write_address <= write_address_next;
      elements_int  <= elements_next;
      full_int      <= full_next;
      empty_int     <= empty_next;
    end if;
  end process sync;

  exec : process(write_address, read_address, full_int, elements_int, empty_int, ctrl_i)
  begin
    write_address_next <= write_address;
    read_address_next  <= read_address;
    elements_next      <= elements_int;
    full_next          <= full_int;
    empty_next         <= empty_int;
    wr_int             <= '0';
    rd_int             <= '0';

    if ctrl_i.wr = '1' and full_int = '0' then
      wr_int             <= '1';        -- only write, if fifo is not full
      write_address_next <= std_logic_vector(unsigned(write_address) + 1);
      elements_next <=  std_logic_vector(unsigned(elements_int) + 1);
    end if;

    if ctrl_i.rd = '1' and empty_int = '0' then
      rd_int            <= '1';         -- only read, if fifo is not empty
      read_address_next <= std_logic_vector(unsigned(read_address) + 1);
      elements_next <= std_logic_vector(unsigned(elements_int) - 1);
    end if;

    -- in case we both read and write in the same cycle, do not touch the element counter
    if ctrl_i.wr = '1' and full_int = '0' and ctrl_i.rd = '1' and empty_int = '0' then
      elements_next <= elements_int;
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
  elements  <= elements_int;
end fifo_beh;
