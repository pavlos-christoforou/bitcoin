#!/usr/bin/env python
""" Utilities to generate bitcoin addresses.

    - single file with zero dependencies.

    - supports deterministic creation of addresses.

    - includes code from a number of sources:

      * https://github.com/warner/python-ecdsa/tree/master/ecdsa

      * https://github.com/weex/addrgen

      * http://www.seanet.com/~bugbee/crypto/salsa20/salsa20.py

"""

import hashlib
import binascii
import struct
import os
import argparse

#  Copyright (c) 2009 by Larry Bugbee, Kent, WA


class Salsa20(object):
    """
        Salsa20 was submitted to eSTREAM, an EU stream cipher
        competition).  Salsa20 was originally defined to be 20
        rounds.  Reduced round versions, Salsa20/8 (8 rounds) and
        Salsa20/12 (12 rounds), were also submitted.  Salsa20/12
        was chosen as one of the winners and 12 rounds was deemed
        the "right blend" of security and efficiency.  The default
        for this class is 20 rounds.

        Besides the encryption function and the decryption
        function being identical, exactly how Salsa20 works is
        very simple.  Salsa20 accepts a key and an iv to set up
        an initial 64-byte state.  For each 64-byte block of
        data, the state gets scrambled and XORed with the previous
        state.  This new state is then XORed with the input data
        to produce the output.  Salsa20's security is achieved via
        this one scrambling operation, repeated n times (rounds).

        Sample usage:

         s20 = Salsa20(key, iv, 12)
         ciphertext = s20.encrypt(message)


        Larry Bugbee
        May 2009
    """

    TAU    = ( 0x61707865, 0x3120646e, 0x79622d36, 0x6b206574 )
    SIGMA  = ( 0x61707865, 0x3320646e, 0x79622d32, 0x6b206574 )
    ROUNDS = 20                         # 8, 12, 20

    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

    def __init__(self, key, iv='\x00'*8, rounds=ROUNDS):
        """ Both key and iv are bytestrings.  The key must be exactly
            16 or 32 bytes, 128 or 256 bits respectively.  The iv
            must be exactly 8 bytes (64 bits).

            Setting the key but relying on a default iv value (nulls)
            is dangerous.  Either provide the iv here or explicitly
            call iv_setup() to set the iv.

            Salsa20 exists in three basic versions defined by the
            number of rounds (8, 12, and 20).  20 rounds, Salsa20,
            is the default.  12 rounds, Salsa20/12, is the version
            selected by eSTREAM. The 8 round version, Salsa20/8 is
            faster and remains unbroken, but the lesser rounds
            reduces confidence.  Salsa20/8 should not be used with
            high value assets.
            
            The default number of rounds is 12.

        """
        self._key_setup(key)
        self.iv_setup(iv)
        if rounds not in [20, 12, 8]:
            raise Exception('number of rounds must be 8, 12, or 20')
        self.ROUNDS = rounds

    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

    def _key_setup(self, key):
        """ key is converted to a list of 4-byte unsigned integers
            (32 bits).

            Calling this routine with a key value effectively resets
            the context/instance.  Be sure to set the iv as well.
        """
        if len(key) not in [16, 32]:
            raise Exception('key must be either 16 or 32 bytes')
        TAU   = self.TAU
        SIGMA = self.SIGMA
        key_state = [0]*16
        if len(key) == 16:
            k = list(struct.unpack('<4I', key))
            key_state[0]  = TAU[0]
            key_state[1]  = k[0]
            key_state[2]  = k[1]
            key_state[3]  = k[2]
            key_state[4]  = k[3]
            key_state[5]  = TAU[1]

            key_state[10] = TAU[2]
            key_state[11] = k[0]
            key_state[12] = k[1]
            key_state[13] = k[2]
            key_state[14] = k[3]
            key_state[15] = TAU[3]

        elif len(key) == 32:
            k = list(struct.unpack('<8I', key))
            key_state[0]  = SIGMA[0]
            key_state[1]  = k[0]
            key_state[2]  = k[1]
            key_state[3]  = k[2]
            key_state[4]  = k[3]
            key_state[5]  = SIGMA[1]

            key_state[10] = SIGMA[2]
            key_state[11] = k[4]
            key_state[12] = k[5]
            key_state[13] = k[6]
            key_state[14] = k[7]
            key_state[15] = SIGMA[3]
        self.key_state = key_state

    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

    def iv_setup(self, iv):
        """ self.state and other working strucures are lists of
            4-byte unsigned integers (32 bits).

            The iv should never be reused with the same key value,
            but it is not a secret.  Use date, time or some other
            counter to be sure the iv is different each time, and
            be sure to communicate the IV to the receiving party.
            Prepending 8 bytes of iv to the ciphertext is the usual
            way to do this.

            Just as setting a new key value effectively resets the
            context, setting the iv also resets the context with
            the last key value entered.
        """
        if len(iv) != 8:
            raise Exception('iv must be 8 bytes')
        iv_state = self.key_state[:]
        v = list(struct.unpack('<2I', iv))
        iv_state[6] = v[0]
        iv_state[7] = v[1]
        iv_state[8] = 0
        iv_state[9] = 0
        self.state = iv_state
        self.lastchunk = 64     # flag to ensure all but the last
                                # chunks is a multiple of 64 bytes

    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

    def encrypt(self, datain):
        """ datain and dataout are bytestrings.

            If the data is submitted to this routine in chunks,
            the chunk size MUST be an exact multiple of 64 bytes.
            Only the final chunk may be less than an even multiple.
        """
        if self.lastchunk != 64:
            raise Exception('size of last chunk not a multiple of 64 bytes')
        dataout = ''
        stream  = ''
        while datain:
            stream = self._salsa20_scramble();
            self.state[8] += 1
            if self.state[8] == 0:               # if overflow in state[8]
                self.state[9] += 1               # carry to state[9]
                # not to exceed 2^70 x 2^64 = 2^134 data size ??? <<<<
            dataout += self._xor(stream, datain[:64])
            if len(datain) <= 64:
                self.lastchunk = len(datain)
                return dataout
            datain = datain[64:]
        raise Exception('Huh?')
    decrypt = encrypt

    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

    def _ROL32(self, a,b):
        return ((a << b) | (a >> (32 - b))) & 0xffffffff

    def _salsa20_scramble(self):     # 64 bytes in
        """ self.state and other working strucures are lists of
            4-byte unsigned integers (32 bits).

            output must be converted to bytestring before return.
        """
        x = self.state[:]    # makes a copy
        for i in xrange(self.ROUNDS, 0, -2):
            x[ 4] ^= self._ROL32( (x[ 0]+x[12]) & 0xffffffff,  7)
            x[ 8] ^= self._ROL32( (x[ 4]+x[ 0]) & 0xffffffff,  9)
            x[12] ^= self._ROL32( (x[ 8]+x[ 4]) & 0xffffffff, 13)
            x[ 0] ^= self._ROL32( (x[12]+x[ 8]) & 0xffffffff, 18)
            x[ 9] ^= self._ROL32( (x[ 5]+x[ 1]) & 0xffffffff,  7)
            x[13] ^= self._ROL32( (x[ 9]+x[ 5]) & 0xffffffff,  9)
            x[ 1] ^= self._ROL32( (x[13]+x[ 9]) & 0xffffffff, 13)
            x[ 5] ^= self._ROL32( (x[ 1]+x[13]) & 0xffffffff, 18)
            x[14] ^= self._ROL32( (x[10]+x[ 6]) & 0xffffffff,  7)
            x[ 2] ^= self._ROL32( (x[14]+x[10]) & 0xffffffff,  9)
            x[ 6] ^= self._ROL32( (x[ 2]+x[14]) & 0xffffffff, 13)
            x[10] ^= self._ROL32( (x[ 6]+x[ 2]) & 0xffffffff, 18)
            x[ 3] ^= self._ROL32( (x[15]+x[11]) & 0xffffffff,  7)
            x[ 7] ^= self._ROL32( (x[ 3]+x[15]) & 0xffffffff,  9)
            x[11] ^= self._ROL32( (x[ 7]+x[ 3]) & 0xffffffff, 13)
            x[15] ^= self._ROL32( (x[11]+x[ 7]) & 0xffffffff, 18)

            x[ 1] ^= self._ROL32( (x[ 0]+x[ 3]) & 0xffffffff,  7)
            x[ 2] ^= self._ROL32( (x[ 1]+x[ 0]) & 0xffffffff,  9)
            x[ 3] ^= self._ROL32( (x[ 2]+x[ 1]) & 0xffffffff, 13)
            x[ 0] ^= self._ROL32( (x[ 3]+x[ 2]) & 0xffffffff, 18)
            x[ 6] ^= self._ROL32( (x[ 5]+x[ 4]) & 0xffffffff,  7)
            x[ 7] ^= self._ROL32( (x[ 6]+x[ 5]) & 0xffffffff,  9)
            x[ 4] ^= self._ROL32( (x[ 7]+x[ 6]) & 0xffffffff, 13)
            x[ 5] ^= self._ROL32( (x[ 4]+x[ 7]) & 0xffffffff, 18)
            x[11] ^= self._ROL32( (x[10]+x[ 9]) & 0xffffffff,  7)
            x[ 8] ^= self._ROL32( (x[11]+x[10]) & 0xffffffff,  9)
            x[ 9] ^= self._ROL32( (x[ 8]+x[11]) & 0xffffffff, 13)
            x[10] ^= self._ROL32( (x[ 9]+x[ 8]) & 0xffffffff, 18)
            x[12] ^= self._ROL32( (x[15]+x[14]) & 0xffffffff,  7)
            x[13] ^= self._ROL32( (x[12]+x[15]) & 0xffffffff,  9)
            x[14] ^= self._ROL32( (x[13]+x[12]) & 0xffffffff, 13)
            x[15] ^= self._ROL32( (x[14]+x[13]) & 0xffffffff, 18)
        for i in xrange(16):
            x[i] = (x[i] + self.state[i]) & 0xffffffff
        output = struct.pack('<16I',
                            x[ 0], x[ 1], x[ 2], x[ 3],
                            x[ 4], x[ 5], x[ 6], x[ 7],
                            x[ 8], x[ 9], x[10], x[11],
                            x[12], x[13], x[14], x[15])
        return output                          # 64 bytes out
   
    # - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

    def _xor(self, stream, din):
        dout = []
        for i in xrange(len(din)):
            dout.append(chr(ord(stream[i])^ord(din[i])))
        return ''.join(dout)



# based on work by Peter Pearson


## Utilities
    
def inverse_mod(a, m):

    """ Inverse of a mod m.

    """

    if a < 0 or m <= a:
        a = a % m

    # From Ferguson and Schneier, roughly:

    c, d = a, m
    uc, vc, ud, vd = 1, 0, 0, 1
    while c != 0:
        q, c, d = divmod( d, c ) + ( c, )
        uc, vc, ud, vd = ud - q*uc, vd - q*vc, uc, vc

    # At this point, d is the GCD, and ud*a+vd*m = d.
    # If d == 1, this means that ud is a inverse.

    assert d == 1

    return ud if ud > 0 else ud + m



def leftmost_bit(x):
    assert x > 0

    result = 1L

    while result <= x:
        result = 2 * result

    return result // 2



###


class WalletError(Exception):

    """ generic wallet error.

    """



class FPCurve(object):

    """ Elliptic Curve over the field of integers modulo a prime.

        Certicom secp256-k1

    """

    p = 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2fL
    a = 0x0000000000000000000000000000000000000000000000000000000000000000L
    b = 0x0000000000000000000000000000000000000000000000000000000000000007L

    Gx = 0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798L
    Gy = 0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8L
    # base point order
    r  = 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141L


    def __init__(self, x = 'dflt', y = 'dflt'):

        self.x = self.Gx if x == 'dflt' else x
        self.y = self.Gy if y == 'dflt' else y
        


    def contains_point(self, x, y):

        """ Is the point (x,y) on this curve?
        
        """
        
        return ( y * y - ( x * x * x + self.a * x + self.b ) ) % self.p == 0


    def __cmp__(self, other):

        """ Return 0 if the points are identical, 1 otherwise.

        """

        if self.x == other.x and self.y == other.y:
            return 0
        else:
            return 1



    def __add__(self, other):

        """ Add one point to another point.

        """
    
        if self.x == other.x:
            if (self.y + other.y ) % self.p == 0:
                return INFINITY
            else:
                return self.double()
        p = self.p

        l = (
            (other.y - self.y ) * 
            inverse_mod(other.x - self.x, p)
            ) % p

        x3 = (l * l - self.x - other.x) % p
        y3 = (l * (self.x - x3) - self.y) % p
    
        return self.__class__(x = x3, y = y3)



    def __mul__(self, other):

        """ Multiply a point by an integer.

        """
        
        e = other
        e = e % self.r
        if e == 0:
            return INFINITY

        if self == INFINITY:
            return INFINITY

        assert e > 0

        e3 = 3 * e

        negative_self = self.__class__(self.x, -self.y)

        i = leftmost_bit(e3) // 2

        result = self
        
        # print "Multiplying %s by %d (e3 = %d):" % ( self, other, e3 )
        while i > 1:
            result = result.double()
            if (e3 & i) != 0 and (e & i) == 0:
                result = result + self

            if (e3 & i) == 0 and (e & i) != 0:
                result = result + negative_self

            i = i // 2

        return result



    def __rmul__(self, other):

        """ Multiply a point by an integer.

        """
    
        return self * other



    def __str__(self):
        if self == INFINITY:
            return "infinity"
        else:
            return "(%d, %d)" % ( self.x, self.y )



    def double(self):
        
        """ Return a new point that is twice the old.

        """

        if self == INFINITY:
            return INFINITY


        p = self.p
        a = self.a

        l = (
            (3 * self.x * self.x + a ) * 
            inverse_mod(2 * self.y, p)
            ) % p

        x3 = (l * l - 2 * self.x) % p
        y3 = (l * (self.x - x3) - self.y) % p
    
        return self.__class__(x3, y3)



# This one point is the Point At Infinity for all purposes:
INFINITY = FPCurve(None, None )  




### from addrgen.py  (David Sterry - weex)
### and from https://gist.github.com/ianoxley/865912

class Base58(object):

    """ Base58 manipulations.

    
    """

    B58_DIGITS = '123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz'

    alphabet = '123456789abcdefghijkmnopqrstuvwxyzABCDEFGHJKLMNPQRSTUVWXYZ'
    base_count = len(alphabet)

    def encode(self, num):
            """ Returns num in a base58-encoded string """
            encode = ''

            if (num < 0):
                    return ''

            while (num >= base_count):	
                    mod = num % base_count
                    encode = alphabet[mod] + encode
                    num = num / base_count

            if (num):
                    encode = alphabet[num] + encode

            return encode

    def decode(self, s):
            """ Decodes the base58-encoded string s into an integer """
            decoded = 0
            multi = 1
            s = s[::-1]
            for char in s:
                    decoded += multi * alphabet.index(char)
                    multi = multi * base_count

            return decoded



    def dhash(self, s):
        return hashlib.sha256(hashlib.sha256(s).digest()).digest()



    def rhash(self, s):
        h1 = hashlib.new('ripemd160')
        h1.update(hashlib.sha256(s).digest())
        return h1.digest()



    def base58_encode(self, n):
        l = []
        while n > 0:
            n, r = divmod(n, 58)
            l.insert(0, (self.B58_DIGITS[r]))

        return ''.join(l)



    def base58_decode(self, s):
        n = 0
        for ch in s:
            n *= 58
            digit = self.B58_DIGITS.index(ch)
            n += digit
        return n



    def base58_encode_padded(self, s):
        res = self.base58_encode(int('0x' + s.encode('hex'), 16))
        pad = 0
        for c in s:
            if c == chr(0):
                pad += 1
            else:
                break
        return self.B58_DIGITS[0] * pad + res



    def base58_decode_padded(self, s):
        pad = 0
        for c in s:
            if c == self.B58_DIGITS[0]:
                pad += 1
            else:
                break

        h = '%x' % self.base58_decode(s)

        if len(h) % 2:
            h = '0' + h

        res = h.decode('hex')

        return chr(0) * pad + res



    def base58_check_encode(self, s, version=0):
        vs = chr(version) + s
        check = self.dhash(vs)[:4]

        return self.base58_encode_padded(vs + check)



    def base58_check_decode(self, s, version=0):
        k = self.base58_decode_padded(s)
        v0, data, check0 = k[0], k[1:-4], k[-4:]
        check1 = self.dhash(v0 + data)[:4]

        if check0 != check1:
            raise WalletError('checksum error')

        if version != ord(v0):
            raise WalletError('version mismatch')

        return data


    def order_len(self, order):
        return (1+len("%x" % order))//2 # bytes


    def number_to_string(self, num, order):
        l = self.order_len(order)
        fmt_str = "%0" + str(2*l) + "x"
        string = binascii.unhexlify(fmt_str % num)

        return string


    def string_to_number(self, string):
        return int(binascii.hexlify(string), 16)





class Address(object):

    """ Bitcoin address.

    """

    base_curve = FPCurve()
    
    B58 = Base58()

    private_key = None


    def __init__(self, private_key):
        self.private_key = private_key

        string_key = self.B58.base58_check_decode(private_key, 128)
        int_key = self.B58.string_to_number(string_key)
        self.private_key_int = int_key

        self.public_point = self.base_curve * int_key
        self._validate_public_key(self.public_point)
        self._validate_private_key(int_key)

        ## do an extra validation by signing and then verifying a
        ## message

        data_hash = self.B58.dhash("verify")
        signature =self.sign(data_hash,
                             self.rand_key(256, self.base_curve.r)
                             )
        assert self.verify(data_hash, signature)


    def _validate_public_key(self, public_point):

        """ is the public key valid?

        """

        out = (public_point != INFINITY and
               0 < public_point.x < public_point.r and
               0 < public_point.y < public_point.r and
               self.base_curve.contains_point(public_point.x,
                                         public_point.y) and
               self.base_curve.r * public_point == INFINITY
               )

        return out


    def _validate_private_key(self, int_private_key):

        """ is the public key valid?

        """

        return 0 < int_private_key < self.base_curve.p



    def rand_key(self, bits, n):

        ''' Generate a random number (mod n) having the specified bit
            length.

            from https://github.com/amintos/PyECC/blob/master/ecc/ecdsa.py
        '''

        rb = os.urandom(bits / 8 + 8)  # + 64 bits as recommended in FIPS 186-3
        c = 0
        for r in rb:
            c = (c << 8) | ord(r)

        return (c % (n - 1)) + 1     



    def verify(self, data_hash, signature):

        """ Verify that signature is a valid signature of data_hash.

            Return True if the signature is valid.

        """

        (r, s) = signature

        order = self.base_curve.r

        if r < 1 or r > order - 1:
            return False

        if s < 1 or s > order - 1:
            return False
        
        c = inverse_mod(s, order)

        u1 = (self.B58.string_to_number(data_hash) * c) % order
        u2 = (r * c) % order
        xy = u1 * self.base_curve + u2 * self.public_point
        v = xy.x % order

        return v == r



    def sign(self, data_hash, nonce):
        
        """ Return a signature for the provided hash, using the
            provided random nonce.  It is absolutely vital that
            nonce be an unpredictable number in the range [1,
            self.public_key.point.order()-1].  If an attacker can
            guess nonce, he can compute our private key from a
            single signature.  Also, if an attacker knows a few
            high-order bits (or a few low-order bits) of nonce, he
            can compute our private key from many signatures.  The
            generation of nonces with adequate cryptographic strength
            is very difficult and far beyond the scope of this
            comment.

            May raise WalletError, in which case retrying with a new
            nonce is in order.

        """

        order = self.base_curve.r
        k = nonce % order
        p1 = k * self.base_curve
        r = p1.x
        if r == 0:
            raise WalletError("Bad random number r. Try again with different nonce")

        s = (
            inverse_mod(k, order) * 
            (self.B58.string_to_number(data_hash) + (
                self.private_key_int * r) % order)
            ) % order
        if s == 0:
            raise WalletError("Bad random number s. Try again with different nonce")

        return (r, s)



    def get_public_key(self):

        """ return encoded public key.

        """

        x = self.B58.number_to_string(self.public_point.x, self.base_curve.r)
        y = self.B58.number_to_string(self.public_point.y, self.base_curve.r)
        prefix = self.B58.number_to_string(4, 1)
        key = prefix + x + y
        return self.B58.base58_check_encode(key, 128)



    def get_private_key(self):

        """ return encoded private key.

        """

        return self.private_key



    def get_address(self):
        """ return encoded address.

        """

        x = self.B58.number_to_string(self.public_point.x, self.base_curve.r)
        y = self.B58.number_to_string(self.public_point.y, self.base_curve.r)
        prefix = self.B58.number_to_string(4, 1)
        key = prefix + x + y
        hash160 = self.B58.rhash(key)
        return self.B58.base58_check_encode(hash160)





class Wallet(object):

    """ Deterministic wallet.

        Takes an input phrase and creates 'count' of bitcoin offline
        addresses and 'count' online bitcoin addresses.

        The scheme is defined by the following steps:

        - a sha256 hash of the input phrase is generated.
        
        - the base private key for offline addresses is generated by
          taking the sha256 hash of the first hash plus the string
          'offline'.

        - the base private key for online addresses is generated by
          taking the sha256 hash of the first hash plus the string
          'online'.

        - each address is generated by taking the sha256 hash of the
          respective base private key and appending a sequence number
          starting from 1.

    """

    B58 = Base58()

    def __init__(self, phrase, count = 5):

        self.phrase = phrase
        self.count = count
        self.base_hash = self.B58.dhash(phrase)
        self.base_offline_hash = self.B58.dhash(self.base_hash + 'offline')
        self.base_online_hash = self.B58.dhash(self.base_hash + 'online')

        self.offline_addresses = [
            Address(private_key = self.B58.base58_check_encode(
                self.B58.dhash('%s%i' % (self.base_offline_hash, i)), 128))
            for i in range(1, self.count + 1)
            ]

        self.online_addresses = [
            Address(private_key = self.B58.base58_check_encode(
                self.B58.dhash('%s%i' % (self.base_online_hash, i)), 128))
            for i in range(1, self.count + 1)
            ]


    def print_offline_addresses(self):
        print 'Printing Offline Addresses'
        for (i, address) in enumerate(self.offline_addresses):
            print '%i, %s, %s' % (i+1, address.get_address(), address.get_private_key())



    def print_online_addresses(self):
        print 'Printing Online Addresses'
        for (i, address) in enumerate(self.online_addresses):
            print '%i, %s, %s' % (i+1, address.get_address(), address.get_private_key())



    def print_report(self):

        """ print a full report of all relevant info.

        """

        out = ['Offline Addresses',
               '=================',
               '',
               ]

        for (i, address) in enumerate(self.offline_addresses):
            out.append('%i, %s, %s' % (i+1, address.get_address(), address.get_private_key()))

        out.append('')
        out.append('')
        out.extend( ['Online Addresses',
                     '================',
                     '',
                     ]
                    )
        for (i, address) in enumerate(self.online_addresses):
            out.append('%i, %s, %s' % (i+1, address.get_address(), address.get_private_key()))

        out.append('')


        txt = template.format(phrase = self.phrase, addresses = '\n'.join(out))

        print txt
        return txt



def cli():
    """ command line interface.

    """

    parser = argparse.ArgumentParser(
        description = 'Generate Deterministic BitCoin Addresses',
        )

    parser.add_argument('--phrase',
                        required = True,
                        dest = 'phrase',
                        help = "Secret Phrase. MAKE SURE IT IS LONG AND COMPLEX AND **ENSURE** YOU NEITHER REVEAL IT TO ANYONE NOR FORGET IT."
    )

    parser.add_argument('--password',
                        dest = 'password',
                        help = "Optionally encrypts phrase. Allows phrase to be stored in less secure places but not as safe as remembering the full phrase. If you trust the person/place to hold the encrypted phrase a simple password may suffice. Think carefully."
    )

    parser.add_argument('--count',
                        type = int,
                        dest = 'count',
                        help = "Number of offline/online addresses to generate. (They are the same anyway but it does help to seperate them out)."
    )




    args = parser.parse_args()

    ## password is not yer supported
    wallet = Wallet(
        phrase = args.phrase.strip(),
        count  = args.count
        )

    wallet.print_report()


####

template = """
########################################################################

wallet.py - Deterministic Bitcoin Address Generator
https://github.com/pavlos-christoforou/bitcoin

########################################################################


Your chosen phrase is given below:

========================================================================

{phrase}

========================================================================

Make sure no one has access to this phrase. All offline and online
addresses generated here can be recovered by having access to this
phrase. Store it in a very secure place or just memorize it. If your
bitcoin addresses generated using this tool are for whatever reason
lost they can be regenerated by rerunning this tool with your chosen
phrase.


Addresses and Keys
------------------

{addresses}


Keep private addresses private. In general it is a good idea to keep
offline addresses offline (ie not imported in a client connected to
the internet and perhaps completely out of access. You may even delete
them completely since they can be regenrated usign this module and the
secret phrase. A Raspberry Pi in a locked place may be a good offline
option.
"""

    


####
            
def test1():

    """ test against bitaddress.org
    """

    a = Address(private_key = '5HzWtfWT6PXeBip7Jd82Eujzv3meTspr3urKhHeWb6KaP6v75HT')
    assert a.get_public_key() == '6dHY6LHLaiJqHrWpjcMq72r3MRmss5PmnzNxJ7PPXixoaNFopeaZ6YY8BSTRExtoHVxXydHDQbEMG6PUbGAS855H7vK2SDw8'
    assert a.get_address() == '125Km6UeN5rFuJVdKaEQyrdbjjBBJk3hzh'



def test2():

    """ test wallet
    """

    w1 = Wallet(phrase = "and when they were up they were up, and when they were down they were down", count = 10)
    w2 = Wallet(phrase = "and when they were up they were up, and when they were down they were down", count = 10)

    for (_w1, _w2) in zip(w1.offline_addresses, w2.offline_addresses):
        assert _w1.public_point == _w2.public_point

    for (_w1, _w2) in zip(w1.online_addresses, w2.online_addresses):
        assert _w1.public_point == _w2.public_point



    w1 = Wallet(phrase = "and when they were up they were up, and when they were down they were down", count = 10)
    w2 = Wallet(phrase = "and when they were up they were up, and when they were down they were still up", count = 10)

    for (_w1, _w2) in zip(w1.offline_addresses, w2.offline_addresses):
        assert _w1.public_point != _w2.public_point

    for (_w1, _w2) in zip(w1.online_addresses, w2.online_addresses):
        assert _w1.public_point != _w2.public_point


def test():
    test1()
    test2()





if __name__ == '__main__':
    cli()
