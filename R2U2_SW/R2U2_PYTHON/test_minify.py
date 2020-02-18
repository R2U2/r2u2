import unittest, filecmp, file_minify

# Unit test for csv_minify.py
# Must include files test_one.csv, test_two.csv, test_three.csv, output_one.csv, output_two.csv, output_three.csv in directory 

class CSVFileTest(unittest.TestCase):
	def test_file_one(self):
		file_minify.minify("test_one.csv")
		self.assertTrue(filecmp.cmp("test_one_min.csv", "output_one.csv"))
	
	def test_file_two(self):
		file_minify.minify("test_two.csv")
		self.assertTrue(filecmp.cmp("test_two_min.csv", "output_two.csv"))
	
	def test_file_three(self):
		file_minify.minify("test_three.csv")
		self.assertTrue(filecmp.cmp("test_three_min.csv", "output_three.csv"))
	

if __name__ == '__main__':
	unittest.main()
