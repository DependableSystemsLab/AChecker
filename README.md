# AChecker
AChecker (Access Control Checker) is an automated static analysis tool for detecting access control vulnerabilities in Ethereum smart contracts.

For more details about AChecker , please reference our paper published in ICSE 2023 [AChecker: Statically Detecting Smart Contract
Access Control Vulnerabilities](https://blogs.ubc.ca/dependablesystemslab/2022/12/08/achecker-statically-detecting-smart-contract-access-control-vulnerabilities)


If you use AChecker, please cite this paper

 ```
@inproceedings{ghaleb2023achecker,
  title={AChecker: Statically Detecting Smart Contract Access Control Vulnerabilities},
  author={Ghaleb, Asem and Rubin, Julia and Pattabiraman, Karthik},
  booktitle={Proceedings of the 45th IEEE/ACM International Conference on Software Engineering},
  year={2023}
}
  ```

## Getting Started
**Note:** We tested all scripts provided in this package on a Ubuntu 20.04 LTS machine.

### Requirements
* Python 3.8+

### Building AChecker 

To build the tool manually, we provide a `requirements.txt` file and the script `setup.py` to simply install depedencies required by AChecker and to build everything as follows.

Run the following command. Please make sure you are using python 3.8 or higher.
  
```
cd AChecker
python -m pip install -r requirements.txt
```
 
 ### Analyzing a smart contract
Use the following command to run AChecker on a contract bytecode.
 ```
python bin/achecker.py -f [path_of_the_contract_bytecode_file] -b
```      
As an example, the following command will run AChecker to analyze the contract with CVE ID 'CVE-2021-34273' in the file named '*CVE-2021-34273.code*'
```
python bin/achecker.py -f CVE-2021-34273.code -b -m 8
```

The option -m enables to set the allocated memory for the analysis (in gigabytes). In this example, the allocated memory limit is set to 8 GB. The defalut value is 6 GB when the option -m is not used.

## Contact
For questions about our paper or this code, please contact Asem Ghaleb (aghaleb@alumni.ubc.ca)
