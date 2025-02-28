import tkinter as tk
from tkinter import ttk, messagebox
import pyperclip
import os
import struct
import hashlib
from itertools import zip_longest

# =============================================
# AES-256 Implementation (ECB Mode)
# =============================================

SBOX = [
    0x63, 0x7C, 0x77, 0x7B, 0xF2, 0x6B, 0x6F, 0xC5, 0x30, 0x01, 0x67, 0x2B, 0xFE, 0xD7, 0xAB, 0x76,
    0xCA, 0x82, 0xC9, 0x7D, 0xFA, 0x59, 0x47, 0xF0, 0xAD, 0xD4, 0xA2, 0xAF, 0x9C, 0xA4, 0x72, 0xC0,
    0xB7, 0xFD, 0x93, 0x26, 0x36, 0x3F, 0xF7, 0xCC, 0x34, 0xA5, 0xE5, 0xF1, 0x71, 0xD8, 0x31, 0x15,
    0x04, 0xC7, 0x23, 0xC3, 0x18, 0x96, 0x05, 0x9A, 0x07, 0x12, 0x80, 0xE2, 0xEB, 0x27, 0xB2, 0x75,
    0x09, 0x83, 0x2C, 0x1A, 0x1B, 0x6E, 0x5A, 0xA0, 0x52, 0x3B, 0xD6, 0xB3, 0x29, 0xE3, 0x2F, 0x84,
    0x53, 0xD1, 0x00, 0xED, 0x20, 0xFC, 0xB1, 0x5B, 0x6A, 0xCB, 0xBE, 0x39, 0x4A, 0x4C, 0x58, 0xCF,
    0xD0, 0xEF, 0xAA, 0xFB, 0x43, 0x4D, 0x33, 0x85, 0x45, 0xF9, 0x02, 0x7F, 0x50, 0x3C, 0x9F, 0xA8,
    0x51, 0xA3, 0x40, 0x8F, 0x92, 0x9D, 0x38, 0xF5, 0xBC, 0xB6, 0xDA, 0x21, 0x10, 0xFF, 0xF3, 0xD2,
    0xCD, 0x0C, 0x13, 0xEC, 0x5F, 0x97, 0x44, 0x17, 0xC4, 0xA7, 0x7E, 0x3D, 0x64, 0x5D, 0x19, 0x73,
    0x60, 0x81, 0x4F, 0xDC, 0x22, 0x2A, 0x90, 0x88, 0x46, 0xEE, 0xB8, 0x14, 0xDE, 0x5E, 0x0B, 0xDB,
    0xE0, 0x32, 0x3A, 0x0A, 0x49, 0x06, 0x24, 0x5C, 0xC2, 0xD3, 0xAC, 0x62, 0x91, 0x95, 0xE4, 0x79,
    0xE7, 0xC8, 0x37, 0x6D, 0x8D, 0xD5, 0x4E, 0xA9, 0x6C, 0x56, 0xF4, 0xEA, 0x65, 0x7A, 0xAE, 0x08,
    0xBA, 0x78, 0x25, 0x2E, 0x1C, 0xA6, 0xB4, 0xC6, 0xE8, 0xDD, 0x74, 0x1F, 0x4B, 0xBD, 0x8B, 0x8A,
    0x70, 0x3E, 0xB5, 0x66, 0x48, 0x03, 0xF6, 0x0E, 0x61, 0x35, 0x57, 0xB9, 0x86, 0xC1, 0x1D, 0x9E,
    0xE1, 0xF8, 0x98, 0x11, 0x69, 0xD9, 0x8E, 0x94, 0x9B, 0x1E, 0x87, 0xE9, 0xCE, 0x55, 0x28, 0xDF,
    0x8C, 0xA1, 0x89, 0x0D, 0xBF, 0xE6, 0x42, 0x68, 0x41, 0x99, 0x2D, 0x0F, 0xB0, 0x54, 0xBB, 0x16
]

INV_SBOX = [
    0x52, 0x09, 0x6A, 0xD5, 0x30, 0x36, 0xA5, 0x38, 0xBF, 0x40, 0xA3, 0x9E, 0x81, 0xF3, 0xD7, 0xFB,
    0x7C, 0xE3, 0x39, 0x82, 0x9B, 0x2F, 0xFF, 0x87, 0x34, 0x8E, 0x43, 0x44, 0xC4, 0xDE, 0xE9, 0xCB,
    0x54, 0x7B, 0x94, 0x32, 0xA6, 0xC2, 0x23, 0x3D, 0xEE, 0x4C, 0x95, 0x0B, 0x42, 0xFA, 0xC3, 0x4E,
    0x08, 0x2E, 0xA1, 0x66, 0x28, 0xD9, 0x24, 0xB2, 0x76, 0x5B, 0xA2, 0x49, 0x6D, 0x8B, 0xD1, 0x25,
    0x72, 0xF8, 0xF6, 0x64, 0x86, 0x68, 0x98, 0x16, 0xD4, 0xA4, 0x5C, 0xCC, 0x5D, 0x65, 0xB6, 0x92,
    0x6C, 0x70, 0x48, 0x50, 0xFD, 0xED, 0xB9, 0xDA, 0x5E, 0x15, 0x46, 0x57, 0xA7, 0x8D, 0x9D, 0x84,
    0x90, 0xD8, 0xAB, 0x00, 0x8C, 0xBC, 0xD3, 0x0A, 0xF7, 0xE4, 0x58, 0x05, 0xB8, 0xB3, 0x45, 0x06,
    0xD0, 0x2C, 0x1E, 0x8F, 0xCA, 0x3F, 0x0F, 0x02, 0xC1, 0xAF, 0xBD, 0x03, 0x01, 0x13, 0x8A, 0x6B,
    0x3A, 0x91, 0x11, 0x41, 0x4F, 0x67, 0xDC, 0xEA, 0x97, 0xF2, 0xCF, 0xCE, 0xF0, 0xB4, 0xE6, 0x73,
    0x96, 0xAC, 0x74, 0x22, 0xE7, 0xAD, 0x35, 0x85, 0xE2, 0xF9, 0x37, 0xE8, 0x1C, 0x75, 0xDF, 0x6E,
    0x47, 0xF1, 0x1A, 0x71, 0x1D, 0x29, 0xC5, 0x89, 0x6F, 0xB7, 0x62, 0x0E, 0xAA, 0x18, 0xBE, 0x1B,
    0xFC, 0x56, 0x3E, 0x4B, 0xC6, 0xD2, 0x79, 0x20, 0x9A, 0xDB, 0xC0, 0xFE, 0x78, 0xCD, 0x5A, 0xF4,
    0x1F, 0xDD, 0xA8, 0x33, 0x88, 0x07, 0xC7, 0x31, 0xB1, 0x12, 0x10, 0x59, 0x27, 0x80, 0xEC, 0x5F,
    0x60, 0x51, 0x7F, 0xA9, 0x19, 0xB5, 0x4A, 0x0D, 0x2D, 0xE5, 0x7A, 0x9F, 0x93, 0xC9, 0x9C, 0xEF,
    0xA0, 0xE0, 0x3B, 0x4D, 0xAE, 0x2A, 0xF5, 0xB0, 0xC8, 0xEB, 0xBB, 0x3C, 0x83, 0x53, 0x99, 0x61,
    0x17, 0x2B, 0x04, 0x7E, 0xBA, 0x77, 0xD6, 0x26, 0xE1, 0x69, 0x14, 0x63, 0x55, 0x21, 0x0C, 0x7D
]
# Rijndael Rcon
RCON = [0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1B, 0x36]

def gf_mult(a, b):
    """Galois Field multiplication in GF(2^8)"""
    p = 0
    for _ in range(8):
        if b & 1:
            p ^= a
        a <<= 1
        if a & 0x100:
            a ^= 0x11B
        b >>= 1
    return p

def sub_bytes(state, inverse=False):
    return [[INV_SBOX[b] if inverse else SBOX[b] for b in row] for row in state]

def shift_rows(state, inverse=False):
    shifted = []
    for i in range(4):
        row = [state[i][(j + i) % 4] if not inverse else state[i][(j - i) % 4] 
              for j in range(4)]
        shifted.append(row)
    return shifted

def mix_columns(state, inverse=False):
    for col in range(4):
        column = [state[row][col] for row in range(4)]
        if inverse:
            mixed = [
                gf_mult(0x0e, column[0]) ^ gf_mult(0x0b, column[1]) ^ 
                gf_mult(0x0d, column[2]) ^ gf_mult(0x09, column[3]),
                # ... (full inverse mix columns implementation)
            ]
        else:
            mixed = [
                gf_mult(0x02, column[0]) ^ gf_mult(0x03, column[1]) ^ 
                column[2] ^ column[3],
                # ... (full forward mix columns implementation)
            ]
        for row in range(4):
            state[row][col] = mixed[row] & 0xFF
    return state

def key_expansion(key):
    """AES-256 Key Expansion"""
    nk, nr = 8, 14  # 8*4=32 bytes, 14 rounds
    w = list(struct.unpack('>8I', key))
    
    for i in range(nk, 4*(nr+1)):
        temp = w[i-1]
        if i % nk == 0:
            temp = struct.unpack('>I', bytes([SBOX[b] for b in struct.pack('>I', temp)]))[0] ^ (RCON[i//nk -1] << 24)
        elif nk > 6 and i % nk == 4:
            temp = struct.unpack('>I', bytes([SBOX[b] for b in struct.pack('>I', temp)]))[0]
        w.append(w[i-nk] ^ temp)
    
    return [struct.pack('>4I', *w[i*4:i*4+4]) for i in range(len(w)//4)]

class AES256:
    def __init__(self, key):
        self.round_keys = key_expansion(key)
    
    def encrypt_block(self, block):
        state = [[block[i + 4*j] for j in range(4)] for i in range(4)]
        state = add_round_key(state, struct.unpack('16B', self.round_keys[0]))
        
        for rnd in range(1, 14):
            state = sub_bytes(state)
            state = shift_rows(state)
            state = mix_columns(state)
            state = add_round_key(state, struct.unpack('16B', self.round_keys[rnd]))
        
        state = sub_bytes(state)
        state = shift_rows(state)
        state = add_round_key(state, struct.unpack('16B', self.round_keys[14]))
        return bytes(sum(state, []))
    
    def decrypt_block(self, block):
        state = [[block[i + 4*j] for j in range(4)] for i in range(4)]
        state = add_round_key(state, struct.unpack('16B', self.round_keys[14]))
        
        for rnd in range(13, 0, -1):
            state = shift_rows(state, inverse=True)
            state = sub_bytes(state, inverse=True)
            state = add_round_key(state, struct.unpack('16B', self.round_keys[rnd]))
            state = mix_columns(state, inverse=True)
        
        state = shift_rows(state, inverse=True)
        state = sub_bytes(state, inverse=True)
        state = add_round_key(state, struct.unpack('16B', self.round_keys[0]))
        return bytes(sum(state, []))

# =============================================
# ChaCha20-Poly1305 Implementation
# =============================================

def poly1305_mac(msg, key):
    """Poly1305 Message Authentication Code"""
    r = int.from_bytes(key[:16], 'little') & 0x0ffffffc0ffffffc0ffffffc0fffffff
    s = int.from_bytes(key[16:], 'little')
    accumulator = 0
    for block in [msg[i:i+16] for i in range(0, len(msg), 16)]:
        block += b'\x01' + bytes(15 - len(block))
        n = int.from_bytes(block, 'little')
        accumulator = (accumulator + n) * r % ((1 << 130) - 5)
    return ((accumulator + s) & 0xffffffffffffffffffffffffffffffff).to_bytes(16, 'little')

class ChaCha20Poly1305:
    def __init__(self, key):
        self.key = key
    
    def encrypt(self, plaintext):
        nonce = os.urandom(12)
        key_stream = chacha20_block(self.key, nonce, 1)
        auth_key = key_stream[:32]
        ciphertext = bytes(b ^ k for b, k in zip(plaintext, key_stream[32:]))
        mac = poly1305_mac(nonce + ciphertext, auth_key)
        return nonce + ciphertext + mac
    
    def decrypt(self, data):
        nonce, ciphertext, mac = data[:12], data[12:-16], data[-16:]
        key_stream = chacha20_block(self.key, nonce, 1)
        auth_key = key_stream[:32]
        if mac != poly1305_mac(nonce + ciphertext, auth_key):
            raise ValueError("Authentication failed")
        return bytes(b ^ k for b, k in zip(ciphertext, key_stream[32:]))

# =============================================
# Security Enhancements
# =============================================

def pbkdf2(password, salt, iterations=100000, key_length=32):
    """PBKDF2-HMAC-SHA256 Key Derivation"""
    key = b''
    block_count = 1
    while len(key) < key_length:
        mac = hmac.new(salt + struct.pack('>I', block_count), password, hashlib.sha256)
        block = mac.digest()
        for _ in range(iterations - 1):
            block = hmac.new(block, password, hashlib.sha256).digest()
        key += block
        block_count += 1
    return key[:key_length]

# =============================================
# GUI Application
# =============================================

class CryptoApp(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Cryptography Tool")
        self.geometry("500x400")
        
        ttk.Label(self, text="Encryption Key:").pack(pady=5)
        self.key_entry = ttk.Entry(self, show="*")
        self.key_entry.pack(pady=5)
        
        self.algorithm = tk.StringVar(value="AES-256")
        ttk.Combobox(self, textvariable=self.algorithm, 
                    values=["AES-256", "ChaCha20"]).pack(pady=5)
        
        ttk.Button(self, text="Encrypt", command=self.encrypt).pack(pady=10)
        ttk.Button(self, text="Decrypt", command=self.decrypt).pack(pady=10)
        ttk.Button(self, text="Clear", command=self.clear).pack(pady=10)
    
    def get_key(self):
        key = self.key_entry.get().encode()
        return key.ljust(32 if self.algorithm.get() == "AES-256" else 32, b'\0')[:32]
    
    def encrypt(self):
        try:
            plaintext = pyperclip.paste().encode()
            if self.algorithm.get() == "AES-256":
                cipher = AES256(self.get_key())
                padded = pad_data(plaintext)
                ciphertext = b''.join(cipher.encrypt_block(padded[i:i+16]) 
                                    for i in range(0, len(padded), 16))
            else:
                cipher = ChaCha20Poly1305(self.get_key())
                ciphertext = cipher.encrypt(plaintext)
            pyperclip.copy(ciphertext.hex())
            messagebox.showinfo("Success", "Encrypted to clipboard!")
        except Exception as e:
            messagebox.showerror("Error", str(e))
    
    def decrypt(self):
        try:
            ciphertext = bytes.fromhex(pyperclip.paste())
            if self.algorithm.get() == "AES-256":
                cipher = AES256(self.get_key())
                decrypted = b''.join(cipher.decrypt_block(ciphertext[i:i+16]) 
                                    for i in range(0, len(ciphertext), 16))
            else:
                cipher = ChaCha20Poly1305(self.get_key())
                decrypted = cipher.decrypt(ciphertext)
            # Remove padding
            decrypted = decrypted.rstrip(b'\0')
            pyperclip.copy(decrypted.decode())
            messagebox.showinfo("Success", "Decrypted to clipboard!")
        except Exception as e:
            messagebox.showerror("Error", str(e))

    def clear(self):
        self.key_entry.delete(0, tk.END)
        messagebox.showinfo("Cleared", "Fields have been cleared!")

def pad_data(data):
    """Pad data to ensure it is a multiple of block size"""
    padding_length = 16 - (len(data) % 16)
    return data + bytes([padding_length]) * padding_length

# Run the application
if __name__ == "__main__":
    app = CryptoApp()
    app.mainloop()


if __name__ == "__main__":
    app = CryptoApp()
    app.mainloop()
