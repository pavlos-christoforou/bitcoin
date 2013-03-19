""" Utilities to generate bitcoin addresses.

    - single file with zero dependencies.

    - supports deterministic creation of addresses.

    - includes code from a number of sources:

      * https://github.com/warner/python-ecdsa/tree/master/ecdsa

      * https://github.com/weex/addrgen

"""

import hashlib
import binascii

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
    order  = 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141L


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
        e = e % self.order
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

class Base58(object):

    """ Base58 manipulations.

    """

    B58_DIGITS = '123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz'


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



    def string_to_number_fixedlen(self, string, order):
        l = self.order_len(order)
        return int(binascii.hexlify(string), 16)




class Address(object):

    """ Bitcoin address.

    """

    B58 = Base58()

    private_key = None

    def __init__(self, private_key):
        self.private_key = private_key
        string_key = self.B58.base58_check_decode(private_key, 128)
        int_key = self.B58.string_to_number(string_key)
        self.public_point = FPCurve() * int_key



    def get_public_key(self):

        """ return encoded public key.

        """

        x = self.B58.number_to_string(self.public_point.x, 16)
        y = self.B58.number_to_string(self.public_point.y, 16)
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

        x = self.B58.number_to_string(self.public_point.x, 16)
        y = self.B58.number_to_string(self.public_point.y, 16)
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

    def __init__(self, phrase, count = 3):

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
        for (i, address) in enumerate(self.offline_addresses):
            print '%i, %s, %s' % (i+1, address.get_address(), address.get_private_key())








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

