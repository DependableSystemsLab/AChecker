from setuptools import setup, find_packages

setup(
    name='AChecker',
    version='0.1.0',
    packages=find_packages(),
    install_requires=[],
    scripts=[       
        'bin/achecker.py'
    ],      
    python_requires='>=3.8',    
    
)
