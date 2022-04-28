import random
import math
import sys

######################## Some functions useful down the line ############################

'''
    Returns the Greatest Common Divisor of a and b using Euclidean Algorithm
'''
def gcd(a, b):
    if not b:
        return a

    return gcd(b, a % b)


'''
    Calculates the exponentiation of a to the power b used modulo. The time complexity 
    of this function is log(b).
'''
def ModularBinaryExponentiation(a, b, modulo):
    ret = 1
    while b:
        if b & 1:
            ret = ret * a % modulo

        b >>= 1
        a = a * a % modulo

    return ret

##################### Functions relating to generating and testing primes #####################

'''
    This function computes the Jacobi symbol of (a, n) and is used in prime testing in Solovay
    Strassen test.
    algo src: https://primes.utm.edu/glossary/page.php?sort=JacobiSymbol
'''
def Jacobi(a, n):
    if not a and n == 1:
        return 1
    elif not a:
        return 0
    elif a == -1 and n % 2 == 0:
        return 1
    elif a == -1:
        return -1
    elif a == 1:
        return 1
    elif a == 2 and (n % 8 == 1 or n % 8 == 7):
        return 1
    elif a == 2 and (n % 8 == 3 or n % 8 == 5):
        return -1
    elif a >= n:
        return Jacobi(a % n, n)
    elif a % 2 == 0:
        return Jacobi(2, n) * Jacobi(a // 2, n)
    elif a % 4 == 3 and n % 4 == 3:
        return -1 * Jacobi(n, a)
    else:
        return Jacobi(n, a)


'''
    Solovay-Strassen test to check if the given number is prime or not. 
    Checks if 'num' is prime with the probability of 1 - 1/pow(2, -confidence)
'''
def SolovayStrassen(num, confidence):
    for i in range(confidence):
        # Select a random number in range [1, n-1]
        a = random.randint(1, num - 1)

        # If there is a common factor between a and num other than 1 then obviously num is not prime
        if gcd(a, num) > 1:
            return False

        # Checks another condition of primality using jacobi symbol of a, n
        if not Jacobi(a, num) % num == ModularBinaryExponentiation(a, (num - 1) // 2, num):
            return False

    # If there are 'confidence' number of successful iterations then the number 'num' is prime in the given confidence
    return True

'''
    This function computes the primitive root for the prime number passed as argument..
    This is a randomized algorithm to guess the primitive root of the number
'''
def PrimitiveRoot(prime):
    if prime == 2:
        return 1

    p1 = 2
    p2 = (prime - 1) // 2

    while True:
        # g is the primitive root if for all the prime factors of (prime - 1) p,
        # power(g, (prime - 1) // p) mod prime is not congruent to 1
        g = random.randint(2, prime - 1)
        if ModularBinaryExponentiation(g, (prime - 1) // p1, prime) != 1 and ModularBinaryExponentiation(g, (prime - 1) // p2, prime) != 1:
            return g

'''
    Generates a prime number with 'bits' number of bits and which is prime with a cofidence of 'confidence'
'''
def generatePrime(bits, confidence):
    # keep trying until a prime with the required confidence is generated
    while True:
        p = random.randint((1 << (bits - 2)), (1 << (bits - 1)))
        while not SolovayStrassen(p, confidence) and p & 1 != 1:
            while p & 1 != 1:
                p = random.randint((1 << (bits - 2)), (1 << (bits - 1)))

        p = p * 2 + 1;
        if SolovayStrassen(p, confidence):
            return p

################################# Encoding and Decoding Messages #########################################
'''
    Encodes the plaintext message into an array of integers.
'''
def encode(PlainText, bits):
    bytes_array = bytearray(PlainText, 'utf-16')
    res = [] # the array of numbers
    num_bytes_per_number = bits // 8

    for i in range(len(bytes_array)):
        if i % num_bytes_per_number == 0:
            res.append(0)

        res[i // num_bytes_per_number] += bytes_array[i] * (1 << (8 * (i % num_bytes_per_number)))

    return res


'''
    Decodes the array of numbers to a plaintext message.
'''
def decode(encoded_text, bits):
    bytes_array = []
    num_bytes_per_number = bits // 8

    for number in encoded_text:
        for i in range(num_bytes_per_number):
            temp = number
            for j in range(i + 1, num_bytes_per_number):
                temp = temp % (1 << (8 * j))

            x = temp // (1 << (8 * i))
            bytes_array.append(x)
            number -= (x * (1 << (8 * i)))

    res = bytearray(b for b in bytes_array).decode('utf-16')
    return res


################################# Classes for public and private keys ###############################3

'''
    The following two classes provide an abstraction for private and public keys used in the algorithm
    p --> a prime
    g --> primitive root
    x --> a random in [0, p - 1]
    h --> g**x % p
'''
class PrivateKey(object):
    def __init__(self, p = None, g = None, x = None, bits = 0):
        self.p = p
        self.g = g
        self.x = x
        self.bits = bits


class PublicKey(object):
    def __init__(self, p = None, g = None, h = None, bits = 0):
        self.p = p
        self.g = g
        self.h = h
        self.bits = bits

def gen_keys(bits = 128, confidence = 32):
    p = generatePrime(bits, confidence)
    g = PrimitiveRoot(p)
    g = ModularBinaryExponentiation(g, 2, p)
    x = random.randint(1, (p - 1) // 2)
    h = ModularBinaryExponentiation(g, x, p)

    public_key = PublicKey(p, g, h, bits)
    private_key = PrivateKey(p, g, x, bits)

    return {'private_key': private_key, 'public_key': public_key}

############################### El Gamal encryption and decryption algorithms ########################


'''
    Applying the El Gamal encryption algorithm to the encoded plaintext
    each number is encrypted into a pair as follows:
    1. c[i] = g ** y % p, d[i] = z[i]h ** y % p where y is chosen randomly and y E [0, p)
'''
def encrypt(key, PlainText):
    encoded_text = encode(PlainText, key.bits)

    encrypted_pairs = []
    for num in encoded_text:
        # selecting a random y E [0, p)
        y = random.randint(0, key.p)
        c = ModularBinaryExponentiation(key.g, y, key.p)
        d = num * ModularBinaryExponentiation(key.h, y, key.p)

        encrypted_pairs.append([c, d])

    encrypted_text = ''
    for pair in encrypted_pairs:
        encrypted_text += str(pair[0]) + ' ' + str(pair[1]) + ' '

    return encrypted_text


'''
    decrypts the encrypted pairs and converts them into encoded integers that are further decoded to the plaintext strings.
    Here private key is used for decryption. The computations involved are as follows:
    1. s = c ** x % p
    2. plaintext integer = d * (s ** (p - 2)) % p
'''
def decrypt(key, CipherText):
    encoded_plaintext = []
    cipher_array = CipherText.split()

    # Because each encoded integer is converted to a pair of ciphers so there must be even number of 
    # space seperated components in the ciphertext
    assert len(cipher_array) % 2 == 0 
    
    for i in range(0, len(cipher_array), 2):
        # As each pair forms (c, d)
        c = int(cipher_array[i])
        d = int(cipher_array[i + 1])        

        s = ModularBinaryExponentiation(c, key.x, key.p)
        encoded_plaintext.append(d * ModularBinaryExponentiation(s, key.p - 2, key.p) % key.p)

    # Now we have regenerated encoded plaintext integers, we just need to decode them
    decoded_text = decode(encoded_plaintext, key.bits)

    return ''.join([c for c in decoded_text if c != '\x00'])


############################################# The main method #####################################################3

message = input("Enter the message to be encrypted: ")
bits = int(input("Number of bits in the prime: "))

keys = gen_keys(bits)
private = keys['private_key']
public = keys['public_key']

ciphertext = encrypt(public, message)

print("cipher text = ", ciphertext)

plaintext = decrypt(private, ciphertext)

print("The final decrypted string = ", plaintext)
print()
assert plaintext == message    

    