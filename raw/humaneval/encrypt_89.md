# Encrypt 89

## Problem (HumanEval 89)

Create a function encrypt_89 that takes a string as an argument &&
returns a string encrypted with the alphabet being rotated. 
The alphabet should be rotated in a manner such that the letters 
shift down by two multiplied to two places.
For example:
encrypt_89("hi") returns "lm"
encrypt_89("asdfghjkl") returns "ewhjklnop"
encrypt_89("gf") returns "kj"
encrypt_89("et") returns "ix"

## Reference Implementation

```c
char* encrypt_89(const char* s){
    size_t i;
    size_t n = strlen(s);
    char* out = (char*)malloc(n + 1);
    if (out == NULL) {
        return NULL;
    }
    for (i=0;i<n;i++)
    {
        int w=((int)s[i]+4-(int)'a')%26+(int)'a';
        out[i]=(char)w;
    }
    out[n]='\0';
    return out;
}
```
