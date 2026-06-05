# Length

## Problem (HumanEval 38)

#include<stdio.h>
#include<string>
using namespace std;
string encode_cyclic(string s){ 
    // returns encoded string by cycling groups of three characters.  
    // split string to groups. Each of length 3.
    int l=s.length();
    int num=(l+2)/3;
    string x,output;
    int i;
    for (i=0;i*3<l;i++)
    {
        //cycle elements in each group. Unless group has fewer elements than 3.
        x=s.substr(i*3,3);
        if (x.length()==3) x=x.substr(1)+x[0];
        output=output+x;
    }
    return output;
}


string decode_cyclic(string s){ 
    /*
    takes as input string encoded with encode_cyclic function. Returns decoded string. 
    */

## Reference Implementation

```c
char* encode_cyclic(const char* s){ 
    // returns encoded string by cycling groups of three characters.  
    // split string to groups. Each of length 3.
    size_t l=strlen(s);
    char* output = (char*)malloc(l + 1);
    if (output == NULL) return NULL;
    for (size_t i=0;i*3<l;i++) {
        size_t b = i * 3;
        size_t rem = l - b;
        if (rem >= 3) {
            output[b] = s[b + 1];
            output[b + 1] = s[b + 2];
            output[b + 2] = s[b];
        } else {
            for (size_t k = 0; k < rem; k++) output[b + k] = s[b + k];
        }
    }
    output[l] = '\0';
    return output;
}


char* decode_cyclic(const char* s){ 
    /*
    takes as input string encoded with encode_cyclic function. Returns decoded string. 
    */
    size_t l=strlen(s);
    char* output = (char*)malloc(l + 1);
    if (output == NULL) return NULL;
    for (size_t i=0;i*3<l;i++) {
        size_t b = i * 3;
        size_t rem = l - b;
        if (rem >= 3) {
            output[b] = s[b + 2];
            output[b + 1] = s[b];
            output[b + 2] = s[b + 1];
        } else {
            for (size_t k = 0; k < rem; k++) output[b + k] = s[b + k];
        }
    }
    output[l] = '\0';
    return output;


}
```
