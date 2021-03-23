import setuptools

with open("sampleREADME.md", "r") as fh:
	sample_long_description = fh.read()
setuptools.setup(
	name="sample R2U2 setup-insert name"
	version="insert version"
	author="sample author"
	author_email="sample email"
	description="sample app setup-insert description here"
	long_description=longdescription,
	long_description_conten_type="sample-insert long description"
	url="insert url"
	packages=[tox,pytest,Sphinx,Black]
	classifiers=[
	"insert classifiers"
	],
	python_requires='insert here'
)
