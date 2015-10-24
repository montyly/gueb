**GUEB** Static analyzer of Use-After-Free on binary	
==============

Presentation
--------------

GUEB is a static analyzer that performs use-after-free detection on binaryi.
Presented at ToorCon San Diego 2015 (slides should come soon).

**For now, GUEB works with BinNavi 4, compatiblity with BinNavi 6 is coming soon....**
How to compile
--------------
GUEB will not work on a 32 bits machine (for now).
GUEB was tested on a Ubuntu 14.04 64 bits.
You need to have ocaml installed, if not :
```  
add-apt-repository ppa:avsm/ppa
apt-get install ocaml m4 opam
opam init
```
You also need to have piqi installed :
```
opam install piqi
```
Then compile the code
```
cd src
export PATH=$PATH:~/.opam/system/bin/ && make
```

How to use
--------------
You need to extract the REIL cfg to a protobuf file.
A jython script is provided in export/export.py (working with BinNavi 4).
Run 
```
jython export.py
```
And choose the proper binary. Two file will be create, the first one is the protobuf file, the second one is the list of functions with no caller (that you can use as entry points on GUEB).
The launch GUEB :
```
gueb -reil reil_file -func main -output_dir results
```
Results of the analysis, start from the main function will be in results directory.
You can find more options with
```
gueb -help
```

Exemples
-------------
TODO
- tiff2pdf
- gnome-nettool


Author
-------------
Feist Josselin (josselin.feist [SPAM] imag.fr)
