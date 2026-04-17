# app.py (Fixed Streaming Version)
from flask import Flask, render_template, request, jsonify, Response, stream_with_context, send_file
import logging
import json
import os
import threading
from datetime import datetime
import hmac
import hashlib
import requests
import string
import random
from Crypto.Cipher import AES
from Crypto.Util.Padding import pad
import codecs
import time
import base64
import re
import urllib3
import uuid
import queue
import concurrent.futures
from concurrent.futures import ThreadPoolExecutor, as_completed
import itertools

# Disable SSL warnings
urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

# Configure logging
logging.basicConfig(
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    level=logging.INFO
)
logger = logging.getLogger(__name__)

# Flask app
app = Flask(__name__)
app.secret_key = os.environ.get('SECRET_KEY', 'your-secret-key-here')

# Configuration
ADMIN_PASSWORD = os.environ.get('ADMIN_PASSWORD', 'admin123')
MAX_THREADS = 10  # Further reduced for stability
REQUEST_TIMEOUT = 20
RETRY_COUNT = 2
MIN_DELAY = 1.0  # Minimum delay between requests

# Storage folders
CURRENT_DIR = os.path.dirname(os.path.abspath(__file__))
BASE_FOLDER = os.path.join(CURRENT_DIR, "BLACK-APIS-ERA")
TOKENS_FOLDER = os.path.join(BASE_FOLDER, "TOKENS-JWT")
ACCOUNTS_FOLDER = os.path.join(BASE_FOLDER, "ACCOUNTS")
RARE_ACCOUNTS_FOLDER = os.path.join(BASE_FOLDER, "RARE ACCOUNTS")
COUPLES_ACCOUNTS_FOLDER = os.path.join(BASE_FOLDER, "COUPLES ACCOUNTS")
GHOST_FOLDER = os.path.join(BASE_FOLDER, "GHOST")
GHOST_ACCOUNTS_FOLDER = os.path.join(GHOST_FOLDER, "ACCOUNTS")
GHOST_RARE_FOLDER = os.path.join(GHOST_FOLDER, "RAREACCOUNT")
GHOST_COUPLES_FOLDER = os.path.join(GHOST_FOLDER, "COUPLESACCOUNT")

for folder in [BASE_FOLDER, TOKENS_FOLDER, ACCOUNTS_FOLDER, RARE_ACCOUNTS_FOLDER, 
               COUPLES_ACCOUNTS_FOLDER, GHOST_FOLDER, GHOST_ACCOUNTS_FOLDER, 
               GHOST_RARE_FOLDER, GHOST_COUPLES_FOLDER]:
    os.makedirs(folder, exist_ok=True)

# Region data
REGION_LANG = {
    "ME": "ar", "IND": "hi", "ID": "id", "VN": "vi", "TH": "th", 
    "BD": "bn", "PK": "ur", "TW": "zh", "CIS": "ru", "SAC": "es", "BR": "pt"
}

hex_key = "32656534343831396539623435393838343531343130363762323831363231383734643064356437616639643866376530306331653534373135623764316533"
key = bytes.fromhex(hex_key)
GARENA = "QkxBQ0tfQVBJcw=="  # BLACK_APIs in base64

# Account rarity patterns
ACCOUNT_RARITY_PATTERNS = {
    "REPEATED_DIGITS_4": [r"(\d)\1{3,}", 3],
    "REPEATED_DIGITS_3": [r"(\d)\1\1(\d)\2\2", 2],
    "SEQUENTIAL_5": [r"(12345|23456|34567|45678|56789)", 4],
    "SEQUENTIAL_4": [r"(0123|1234|2345|3456|4567|5678|6789|9876|8765|7654|6543|5432|4321|3210)", 3],
    "PALINDROME_6": [r"^(\d)(\d)(\d)\3\2\1$", 5],
    "PALINDROME_4": [r"^(\d)(\d)\2\1$", 3],
    "SPECIAL_COMBINATIONS_HIGH": [r"(69|420|1337|007)", 4],
    "SPECIAL_COMBINATIONS_MED": [r"(100|200|300|400|500|666|777|888|999)", 2],
    "QUADRUPLE_DIGITS": [r"(1111|2222|3333|4444|5555|6666|7777|8888|9999|0000)", 4],
    "MIRROR_PATTERN_HIGH": [r"^(\d{2,3})\1$", 3],
    "MIRROR_PATTERN_MED": [r"(\d{2})0\1", 2],
    "GOLDEN_RATIO": [r"1618|0618", 3]
}

# Global counters and storage
RARITY_SCORE_THRESHOLD = 3
POTENTIAL_COUPLES = {}
COUPLES_LOCK = threading.Lock()
FILE_LOCKS = {}
active_generations = {}
generation_sessions = {}
stream_queues = {}  # Queue for streaming results

def get_file_lock(filename):
    if filename not in FILE_LOCKS:
        FILE_LOCKS[filename] = threading.Lock()
    return FILE_LOCKS[filename]

class FreeFireRareAccountGenerator:
    def __init__(self, session_id):
        self.lock = threading.Lock()
        self.success_counter = 0
        self.rare_counter = 0
        self.couples_counter = 0
        self.running = False
        self.session_id = session_id
        self.start_time = None
        self.last_request_time = 0
        self.stream_queue = queue.Queue()
        
    def check_account_rarity(self, account_data):
        account_id = account_data.get("account_id", "")
        
        if account_id == "N/A" or not account_id:
            return False, None, None, 0
        
        rarity_score = 0
        detected_patterns = []
        
        for rarity_type, pattern_data in ACCOUNT_RARITY_PATTERNS.items():
            pattern = pattern_data[0]
            score = pattern_data[1]
            if re.search(pattern, account_id):
                rarity_score += score
                detected_patterns.append(rarity_type)
        
        account_id_digits = [int(d) for d in account_id if d.isdigit()]
        
        if len(set(account_id_digits)) == 1 and len(account_id_digits) >= 4:
            rarity_score += 5
            detected_patterns.append("UNIFORM_DIGITS")
        
        if len(account_id_digits) >= 4:
            differences = [account_id_digits[i+1] - account_id_digits[i] for i in range(len(account_id_digits)-1)]
            if len(set(differences)) == 1:
                rarity_score += 4
                detected_patterns.append("ARITHMETIC_SEQUENCE")
        
        if len(account_id) <= 8 and account_id.isdigit() and int(account_id) < 1000000:
            rarity_score += 3
            detected_patterns.append("LOW_ACCOUNT_ID")
        
        if rarity_score >= RARITY_SCORE_THRESHOLD:
            reason = f"Account ID {account_id} - Score: {rarity_score} - Patterns: {', '.join(detected_patterns)}"
            return True, "RARE_ACCOUNT", reason, rarity_score
        
        return False, None, None, rarity_score
    
    def check_account_couples(self, account_data, thread_id):
        account_id = account_data.get("account_id", "")
        
        if account_id == "N/A" or not account_id:
            return False, None, None
        
        with COUPLES_LOCK:
            for stored_id, stored_data in POTENTIAL_COUPLES.items():
                stored_account_id = stored_data.get('account_id', '')
                
                couple_found, reason = self.check_account_couple_patterns(account_id, stored_account_id)
                if couple_found:
                    partner_data = stored_data
                    del POTENTIAL_COUPLES[stored_id]
                    return True, reason, partner_data
            
            POTENTIAL_COUPLES[account_id] = {
                'uid': account_data.get('uid', ''),
                'account_id': account_id,
                'name': account_data.get('name', ''),
                'password': account_data.get('password', ''),
                'region': account_data.get('region', ''),
                'thread_id': thread_id,
                'timestamp': datetime.now().isoformat()
            }
        
        return False, None, None
    
    def check_account_couple_patterns(self, account_id1, account_id2):
        if account_id1 and account_id2 and abs(int(account_id1) - int(account_id2)) == 1:
            return True, f"Sequential Account IDs: {account_id1} & {account_id2}"
        
        if account_id1 == account_id2[::-1]:
            return True, f"Mirror Account IDs: {account_id1} & {account_id2}"
        
        if account_id1 and account_id2:
            sum_acc = int(account_id1) + int(account_id2)
            if sum_acc % 1000 == 0 or sum_acc % 10000 == 0:
                return True, f"Complementary sum: {account_id1} + {account_id2} = {sum_acc}"
        
        love_numbers = ['520', '521', '1314', '3344']
        for love_num in love_numbers:
            if love_num in account_id1 and love_num in account_id2:
                return True, f"Both contain love number: {love_num}"
        
        return False, None
    
    def save_rare_account(self, account_data, rarity_type, reason, rarity_score, is_ghost=False):
        try:
            if is_ghost:
                rare_filename = os.path.join(GHOST_RARE_FOLDER, "rare-ghost.json")
            else:
                region = account_data.get('region', 'UNKNOWN')
                rare_filename = os.path.join(RARE_ACCOUNTS_FOLDER, f"rare-{region}.json")
            
            rare_entry = {
                'uid': account_data["uid"],
                'password': account_data["password"],
                'account_id': account_data.get("account_id", "N/A"),
                'name': account_data["name"],
                'region': "BLACK_Apis" if is_ghost else account_data.get('region', 'UNKNOWN'),
                'rarity_type': rarity_type,
                'rarity_score': rarity_score,
                'reason': reason,
                'date_identified': datetime.now().strftime('%Y-%m-%d %H:%M:%S'),
                'jwt_token': account_data.get('jwt_token', ''),
                'session_id': self.session_id
            }
            
            file_lock = get_file_lock(rare_filename)
            with file_lock:
                rare_list = []
                if os.path.exists(rare_filename):
                    try:
                        with open(rare_filename, 'r', encoding='utf-8') as f:
                            rare_list = json.load(f)
                    except (json.JSONDecodeError, IOError):
                        rare_list = []
                
                existing_ids = [acc.get('account_id') for acc in rare_list]
                if account_data.get("account_id", "N/A") not in existing_ids:
                    rare_list.append(rare_entry)
                    
                    temp_filename = rare_filename + '.tmp'
                    with open(temp_filename, 'w', encoding='utf-8') as f:
                        json.dump(rare_list, f, indent=2, ensure_ascii=False)
                    os.replace(temp_filename, rare_filename)
                    return True
                else:
                    return False
            
        except Exception as e:
            logger.error(f"Error saving rare account: {e}")
            return False
    
    def save_couples_account(self, account1, account2, reason, is_ghost=False):
        try:
            if is_ghost:
                couples_filename = os.path.join(GHOST_COUPLES_FOLDER, "couples-ghost.json")
            else:
                region = account1.get('region', 'UNKNOWN')
                couples_filename = os.path.join(COUPLES_ACCOUNTS_FOLDER, f"couples-{region}.json")
            
            couples_entry = {
                'couple_id': f"{account1.get('account_id', 'N/A')}_{account2.get('account_id', 'N/A')}",
                'account1': {
                    'uid': account1["uid"],
                    'password': account1["password"],
                    'account_id': account1.get("account_id", "N/A"),
                    'name': account1["name"],
                    'session_id': self.session_id
                },
                'account2': {
                    'uid': account2["uid"],
                    'password': account2["password"],
                    'account_id': account2.get("account_id", "N/A"),
                    'name': account2["name"],
                    'session_id': self.session_id
                },
                'reason': reason,
                'region': "BLACK_Apis" if is_ghost else account1.get('region', 'UNKNOWN'),
                'date_matched': datetime.now().strftime('%Y-%m-%d %H:%M:%S')
            }
            
            file_lock = get_file_lock(couples_filename)
            with file_lock:
                couples_list = []
                if os.path.exists(couples_filename):
                    try:
                        with open(couples_filename, 'r', encoding='utf-8') as f:
                            couples_list = json.load(f)
                    except (json.JSONDecodeError, IOError):
                        couples_list = []
                
                existing_couples = [couple.get('couple_id') for couple in couples_list]
                if couples_entry['couple_id'] not in existing_couples:
                    couples_list.append(couples_entry)
                    
                    temp_filename = couples_filename + '.tmp'
                    with open(temp_filename, 'w', encoding='utf-8') as f:
                        json.dump(couples_list, f, indent=2, ensure_ascii=False)
                    os.replace(temp_filename, couples_filename)
                    return True
                else:
                    return False
            
        except Exception as e:
            logger.error(f"Error saving couples account: {e}")
            return False
    
    def generate_random_name(self, base_name):
        exponent_digits = {'0': '⁰', '1': '¹', '2': '²', '3': '³', '4': '⁴', '5': '⁵', '6': '⁶', '7': '⁷', '8': '⁸', '9': '⁹'}
        number = random.randint(1, 99999)
        number_str = f"{number:05d}"
        exponent_str = ''.join(exponent_digits[digit] for digit in number_str)
        return f"{base_name[:7]}{exponent_str}"
    
    def generate_custom_password(self, prefix):
        garena_decoded = base64.b64decode(GARENA).decode('utf-8')
        characters = string.ascii_uppercase + string.digits
        random_part1 = ''.join(random.choice(characters) for _ in range(5))
        random_part2 = ''.join(random.choice(characters) for _ in range(5))
        return f"{prefix}_{random_part1}_{garena_decoded}_{random_part2}"
    
    def EnC_Vr(self, N):
        if N < 0: 
            return b''
        H = []
        while True:
            BesTo = N & 0x7F 
            N >>= 7
            if N: 
                BesTo |= 0x80
            H.append(BesTo)
            if not N: 
                break
        return bytes(H)
    
    def CrEaTe_VarianT(self, field_number, value):
        field_header = (field_number << 3) | 0
        return self.EnC_Vr(field_header) + self.EnC_Vr(value)
    
    def CrEaTe_LenGTh(self, field_number, value):
        field_header = (field_number << 3) | 2
        encoded_value = value.encode() if isinstance(value, str) else value
        return self.EnC_Vr(field_header) + self.EnC_Vr(len(encoded_value)) + encoded_value
    
    def CrEaTe_ProTo(self, fields):
        packet = bytearray()    
        for field, value in fields.items():
            if isinstance(value, dict):
                nested_packet = self.CrEaTe_ProTo(value)
                packet.extend(self.CrEaTe_LenGTh(field, nested_packet))
            elif isinstance(value, int):
                packet.extend(self.CrEaTe_VarianT(field, value))           
            elif isinstance(value, str) or isinstance(value, bytes):
                packet.extend(self.CrEaTe_LenGTh(field, value))           
        return packet
    
    def E_AEs(self, Pc):
        Z = bytes.fromhex(Pc)
        key = bytes([89, 103, 38, 116, 99, 37, 68, 69, 117, 104, 54, 37, 90, 99, 94, 56])
        iv = bytes([54, 111, 121, 90, 68, 114, 50, 50, 69, 51, 121, 99, 104, 106, 77, 37])
        K = AES.new(key , AES.MODE_CBC , iv)
        R = K.encrypt(pad(Z , AES.block_size))
        return R
    
    def encrypt_api(self, plain_text):
        plain_text = bytes.fromhex(plain_text)
        key = bytes([89, 103, 38, 116, 99, 37, 68, 69, 117, 104, 54, 37, 90, 99, 94, 56])
        iv = bytes([54, 111, 121, 90, 68, 114, 50, 50, 69, 51, 121, 99, 104, 106, 77, 37])
        cipher = AES.new(key, AES.MODE_CBC, iv)
        cipher_text = cipher.encrypt(pad(plain_text, AES.block_size))
        return cipher_text.hex()
    
    def encode_string(self, original):
        keystream = [0x30, 0x30, 0x30, 0x32, 0x30, 0x31, 0x37, 0x30, 0x30, 0x30, 0x30, 0x30, 0x32, 0x30, 0x31, 0x37,
                     0x30, 0x30, 0x30, 0x30, 0x30, 0x32, 0x30, 0x31, 0x37, 0x30, 0x30, 0x30, 0x30, 0x30, 0x32, 0x30]
        encoded = ""
        for i in range(len(original)):
            orig_byte = ord(original[i])
            key_byte = keystream[i % len(keystream)]
            result_byte = orig_byte ^ key_byte
            encoded += chr(result_byte)
        return {"open_id": original, "field_14": encoded}
    
    def to_unicode_escaped(self, s):
        return ''.join(c if 32 <= ord(c) <= 126 else f'\\u{ord(c):04x}' for c in s)
    
    def decode_jwt_token(self, jwt_token):
        try:
            parts = jwt_token.split('.')
            if len(parts) >= 2:
                payload_part = parts[1]
                padding = 4 - len(payload_part) % 4
                if padding != 4:
                    payload_part += '=' * padding
                decoded = base64.urlsafe_b64decode(payload_part)
                data = json.loads(decoded)
                account_id = data.get('account_id') or data.get('external_id')
                if account_id:
                    return str(account_id)
        except Exception as e:
            logger.warning(f"JWT decode failed: {e}")
        return "N/A"
    
    def save_normal_account(self, account_data, region, is_ghost=False):
        try:
            if is_ghost:
                account_filename = os.path.join(GHOST_ACCOUNTS_FOLDER, "ghost.json")
            else:
                account_filename = os.path.join(ACCOUNTS_FOLDER, f"accounts-{region}.json")
            
            account_entry = {
                'uid': account_data["uid"],
                'password': account_data["password"],
                'account_id': account_data.get("account_id", "N/A"),
                'name': account_data["name"],
                'region': "BLACK_Apis" if is_ghost else region,
                'date_created': datetime.now().strftime('%Y-%m-%d %H:%M:%S'),
                'session_id': self.session_id,
                'thread_id': account_data.get('thread_id', 1)
            }
            
            file_lock = get_file_lock(account_filename)
            with file_lock:
                accounts_list = []
                if os.path.exists(account_filename):
                    try:
                        with open(account_filename, 'r', encoding='utf-8') as f:
                            accounts_list = json.load(f)
                    except (json.JSONDecodeError, IOError):
                        accounts_list = []
                
                existing_account_ids = [acc.get('account_id') for acc in accounts_list]
                if account_data.get("account_id", "N/A") not in existing_account_ids:
                    accounts_list.append(account_entry)
                    
                    temp_filename = account_filename + '.tmp'
                    with open(temp_filename, 'w', encoding='utf-8') as f:
                        json.dump(accounts_list, f, indent=2, ensure_ascii=False)
                    
                    os.replace(temp_filename, account_filename)
                    return True
                else:
                    return False
            
        except Exception as e:
            logger.error(f"Error saving normal account: {e}")
            return False
    
    def create_acc(self, region, account_name, password_prefix, is_ghost=False, thread_id=1):
        if not self.running:
            return None
        
        try:
            # Add delay between requests
            current_time = time.time()
            time_since_last_request = current_time - self.last_request_time
            if time_since_last_request < MIN_DELAY:
                time.sleep(MIN_DELAY - time_since_last_request)
            
            password = self.generate_custom_password(password_prefix)
            data = f"password={password}&client_type=2&source=2&app_id=100067"
            message = data.encode('utf-8')
            signature = hmac.new(key, message, hashlib.sha256).hexdigest()
            
            url = "https://100067.connect.garena.com/oauth/guest/register"
            headers = {
                "User-Agent": f"Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36",
                "Authorization": "Signature " + signature,
                "Content-Type": "application/x-www-form-urlencoded",
                "Accept-Encoding": "gzip",
                "Connection": "Keep-Alive"
            }
            
            session = requests.Session()
            session.verify = False
            response = session.post(url, headers=headers, data=data, timeout=REQUEST_TIMEOUT)
            response.raise_for_status()
            
            self.last_request_time = time.time()
            
            if 'uid' in response.json():
                uid = response.json()['uid']
                logger.info(f"[Thread-{thread_id}] Guest account created: {uid}")
                return self.token(uid, password, region, account_name, password_prefix, is_ghost, thread_id)
            return None
        except Exception as e:
            logger.warning(f"[Thread-{thread_id}] Create account failed: {e}")
            time.sleep(2)  # Wait longer on failure
            return None
    
    def token(self, uid, password, region, account_name, password_prefix, is_ghost=False, thread_id=1):
        if not self.running:
            return None
        
        try:
            url = "https://100067.connect.garena.com/oauth/guest/token/grant"
            headers = {
                "Accept-Encoding": "gzip",
                "Connection": "Keep-Alive",
                "Content-Type": "application/x-www-form-urlencoded",
                "Host": "100067.connect.garena.com",
                "User-Agent": f"Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36",
            }
            body = {
                "uid": uid,
                "password": password,
                "response_type": "token",
                "client_type": "2",
                "client_secret": key,
                "client_id": "100067"
            }
            
            session = requests.Session()
            session.verify = False
            response = session.post(url, headers=headers, data=body, timeout=REQUEST_TIMEOUT)
            response.raise_for_status()
            
            if 'open_id' in response.json():
                open_id = response.json()['open_id']
                access_token = response.json()["access_token"]
                refresh_token = response.json()['refresh_token']
                
                result = self.encode_string(open_id)
                field = self.to_unicode_escaped(result['field_14'])
                field = codecs.decode(field, 'unicode_escape').encode('latin1')
                logger.info(f"[Thread-{thread_id}] Token granted for: {uid}")
                return self.Major_Regsiter(access_token, open_id, field, uid, password, region, account_name, password_prefix, is_ghost, thread_id)
            return None
        except Exception as e:
            logger.warning(f"[Thread-{thread_id}] Token grant failed: {e}")
            time.sleep(2)
            return None
    
    def Major_Regsiter(self, access_token, open_id, field, uid, password, region, account_name, password_prefix, is_ghost=False, thread_id=1):
        if not self.running:
            return None
        
        try:
            if is_ghost:
                url = "https://loginbp.ggblueshark.com/MajorRegister"
            else:
                if region.upper() in ["ME", "TH"]:
                    url = "https://loginbp.common.ggbluefox.com/MajorRegister"
                else:
                    url = "https://loginbp.ggblueshark.com/MajorRegister"
            
            name = self.generate_random_name(account_name)
            
            headers = {
                "Accept-Encoding": "gzip",
                "Authorization": "Bearer",   
                "Connection": "Keep-Alive",
                "Content-Type": "application/x-www-form-urlencoded",
                "Expect": "100-continue",
                "Host": "loginbp.ggblueshark.com" if is_ghost or region.upper() not in ["ME", "TH"] else "loginbp.common.ggbluefox.com",
                "ReleaseVersion": "OB53",
                "User-Agent": f"Dalvik/2.1.0 (Linux; U; Android 9; ASUS_I005DA Build/PI)",
                "X-GA": "v1 1",
                "X-Unity-Version": "2018.4."
            }

            lang_code = "pt" if is_ghost else REGION_LANG.get(region.upper(), "en")
            payload = {
                1: name,
                2: access_token,
                3: open_id,
                5: 102000007,
                6: 4,
                7: 1,
                13: 1,
                14: field,
                15: lang_code,
                16: 1,
                17: 1
            }

            payload_bytes = self.CrEaTe_ProTo(payload)
            encrypted_payload = self.E_AEs(payload_bytes.hex())
            
            session = requests.Session()
            session.verify = False
            response = session.post(url, headers=headers, data=encrypted_payload, timeout=REQUEST_TIMEOUT)
            
            if response.status_code == 200:
                logger.info(f"[Thread-{thread_id}] MajorRegister successful: {name}")
                
                # Get account ID and JWT from login
                login_result = self.perform_major_login(uid, password, access_token, open_id, region, is_ghost, thread_id)
                account_id = login_result.get("account_id", "N/A")
                jwt_token = login_result.get("jwt_token", "")
                
                account_data = {
                    "uid": uid, 
                    "password": password, 
                    "name": name, 
                    "region": "GHOST" if is_ghost else region, 
                    "status": "success",
                    "account_id": account_id,
                    "jwt_token": jwt_token,
                    "thread_id": thread_id
                }
                
                return account_data
            else:
                logger.warning(f"[Thread-{thread_id}] MajorRegister returned status: {response.status_code}")
                return None
        except Exception as e:
            logger.warning(f"[Thread-{thread_id}] Major_Regsiter error: {str(e)}")
            time.sleep(2)
            return None
    
    def perform_major_login(self, uid, password, access_token, open_id, region, is_ghost=False, thread_id=1):
        try:
            lang = "pt" if is_ghost else REGION_LANG.get(region.upper(), "en")
            
            payload_parts = [
                b'\x1a\x132025-08-30 05:19:21"\tfree fire(\x01:\x081.114.13B2Android OS 9 / API-28 (PI/rel.cjw.20220518.114133)J\x08HandheldR\nATM MobilsZ\x04WIFI`\xb6\nh\xee\x05r\x03300z\x1fARMv7 VFPv3 NEON VMH | 2400 | 2\x80\x01\xc9\x0f\x8a\x01\x0fAdreno (TM) 640\x92\x01\rOpenGL ES 3.2\x9a\x01+Google|dfa4ab4b-9dc4-454e-8065-e70c733fa53f\xa2\x01\x0e105.235.139.91\xaa\x01\x02',
                lang.encode("ascii"),
                b'\xb2\x01 1d8ec0240ede109973f3321b9354b44d\xba\x01\x014\xc2\x01\x08Handheld\xca\x01\x10Asus ASUS_I005DA\xea\x01@afcfbf13334be42036e4f742c80b956344bed760ac91b3aff9b607a610ab4390\xf0\x01\x01\xca\x02\nATM Mobils\xd2\x02\x04WIFI\xca\x03 7428b253defc164018c604a1ebbfebdf\xe0\x03\xa8\x81\x02\xe8\x03\xf6\xe5\x01\xf0\x03\xaf\x13\xf8\x03\x84\x07\x80\x04\xe7\xf0\x01\x88\x04\xa8\x81\x02\x90\x04\xe7\xf0\x01\x98\x04\xa8\x81\x02\xc8\x04\x01\xd2\x04=/data/app/com.dts.freefireth-PdeDnOilCSFn37p1AH_FLg==/lib/arm\xe0\x04\x01\xea\x04_2087f61c19f57f2af4e7feff0b24d9d9|/data/app/com.dts.freefireth-PdeDnOilCSFn37p1AH_FLg==/base.apk\xf0\x04\x03\xf8\x04\x01\x8a\x05\x0232\x9a\x05\n2019118692\xb2\x05\tOpenGLES2\xb8\x05\xff\x7f\xc0\x05\x04\xe0\x05\xf3F\xea\x05\x07android\xf2\x05pKqsHT5ZLWrYljNb5Vqh//yFRlaPHSO9NWSQsVvOmdhEEn7W+VHNUK+Q+fduA3ptNrGB0Ll0LRz3WW0jOwesLj6aiU7sZ40p8BfUE/FI/jzSTwRe2\xf8\x05\xfb\xe4\x06\x88\x06\x01\x90\x06\x01\x9a\x06\x014\xa2\x06\x014\xb2\x06"GQ@O\x00\x0e^\x00D\x06UA\x0ePM\r\x13hZ\x07T\x06\x0cm\\V\x0ejYV;\x0bU5'
            ]
            
            payload = b''.join(payload_parts)
            
            if is_ghost:
                url = "https://loginbp.ggblueshark.com/MajorLogin"
            elif region.upper() in ["ME", "TH"]:
                url = "https://loginbp.common.ggbluefox.com/MajorLogin"
            else:
                url = "https://loginbp.ggblueshark.com/MajorLogin"
            
            headers = {
                "Accept-Encoding": "gzip",
                "Authorization": "Bearer",
                "Connection": "Keep-Alive",
                "Content-Type": "application/x-www-form-urlencoded",
                "Expect": "100-continue",
                "Host": "loginbp.ggblueshark.com" if is_ghost or region.upper() not in ["ME", "TH"] else "loginbp.common.ggbluefox.com",
                "ReleaseVersion": "OB53",
                "User-Agent": f"Dalvik/2.1.0 (Linux; U; Android 9; ASUS_I005DA Build/PI)",
                "X-GA": "v1 1",
                "X-Unity-Version": "2018.4.11f1"
            }

            data = payload
            data = data.replace(b'afcfbf13334be42036e4f742c80b956344bed760ac91b3aff9b607a610ab4390', access_token.encode())
            data = data.replace(b'1d8ec0240ede109973f3321b9354b44d', open_id.encode())
            
            d = self.encrypt_api(data.hex())
            final_payload = bytes.fromhex(d)

            session = requests.Session()
            session.verify = False
            response = session.post(url, headers=headers, data=final_payload, timeout=REQUEST_TIMEOUT)
            
            if response.status_code == 200 and len(response.text) > 10:
                jwt_start = response.text.find("eyJ")
                if jwt_start != -1:
                    jwt_token = response.text[jwt_start:]
                    second_dot = jwt_token.find(".", jwt_token.find(".") + 1)
                    if second_dot != -1:
                        jwt_token = jwt_token[:second_dot + 44]
                        
                        account_id = self.decode_jwt_token(jwt_token)
                        return {"account_id": account_id, "jwt_token": jwt_token}
            
            return {"account_id": "N/A", "jwt_token": ""}
        except Exception as e:
            logger.warning(f"[Thread-{thread_id}] MajorLogin failed: {e}")
            return {"account_id": "N/A", "jwt_token": ""}
    
    def generate_single_account_threaded(self, region, account_name, password_prefix, thread_id, is_ghost=False):
        """Generate single account in a thread"""
        if not self.running:
            return None
        
        max_retries = 2
        for attempt in range(max_retries):
            try:
                account_result = self.create_acc(region, account_name, password_prefix, is_ghost, thread_id)
                if not account_result:
                    logger.warning(f"[Thread-{thread_id}] Attempt {attempt + 1} failed")
                    if attempt < max_retries - 1:
                        time.sleep(3)  # Wait longer between retries
                    continue

                account_id = account_result.get("account_id", "N/A")
                jwt_token = account_result.get("jwt_token", "")
                
                with self.lock:
                    self.success_counter += 1
                    current_count = self.success_counter

                # Check for rarity
                is_rare, rarity_type, rarity_reason, rarity_score = self.check_account_rarity(account_result)
                if is_rare:
                    with self.lock:
                        self.rare_counter += 1
                    self.save_rare_account(account_result, rarity_type, rarity_reason, rarity_score, is_ghost)
                
                # Check for couples
                is_couple, couple_reason, partner_data = self.check_account_couples(account_result, thread_id)
                if is_couple and partner_data:
                    with self.lock:
                        self.couples_counter += 1
                    self.save_couples_account(account_result, partner_data, couple_reason, is_ghost)
                
                # Save account
                if is_ghost:
                    self.save_normal_account(account_result, "GHOST", is_ghost=True)
                else:
                    self.save_normal_account(account_result, region)
                
                result = {
                    "account": account_result,
                    "is_rare": is_rare,
                    "rarity_type": rarity_type,
                    "rarity_reason": rarity_reason,
                    "rarity_score": rarity_score,
                    "is_couple": is_couple,
                    "couple_reason": couple_reason,
                    "count": current_count,
                    "total_rare": self.rare_counter,
                    "total_couples": self.couples_counter,
                    "thread_id": thread_id
                }
                
                # Send to stream queue
                try:
                    self.stream_queue.put(result, timeout=1)
                except queue.Full:
                    pass
                
                return result
                
            except Exception as e:
                logger.error(f"[Thread-{thread_id}] Error on attempt {attempt + 1}: {e}")
                if attempt < max_retries - 1:
                    time.sleep(3)
        
        return None
    
    def generate_accounts_batch(self, region, account_name, password_prefix, batch_size, thread_id, is_ghost=False):
        """Generate a batch of accounts in a thread"""
        batch_results = []
        for i in range(batch_size):
            if not self.running:
                break
            result = self.generate_single_account_threaded(region, account_name, password_prefix, thread_id, is_ghost)
            if result:
                batch_results.append(result)
        return batch_results

# Web Routes
@app.route('/')
def index():
    """Main page"""
    return render_template('index.html', REGION_LANG=REGION_LANG)

@app.route('/generate', methods=['POST'])
def generate_accounts():
    """Start account generation"""
    data = request.json
    
    account_name = data.get('account_name', 'BLACK_APIs')
    password_prefix = data.get('password_prefix', 'FF2024')
    region = data.get('region', 'BR')
    count = int(data.get('count', 10))
    threshold = int(data.get('threshold', 3))
    use_ghost = data.get('ghost_mode', False)
    threads_count = int(data.get('threads', 3))  # Reduced default
    
    # Safety limits
    if count > 100:
        count = 100
    if threads_count > MAX_THREADS:
        threads_count = MAX_THREADS
    
    # Update global threshold
    global RARITY_SCORE_THRESHOLD
    RARITY_SCORE_THRESHOLD = threshold
    
    # Create session
    session_id = str(uuid.uuid4())
    generator = FreeFireRareAccountGenerator(session_id)
    
    # Store generator
    active_generations[session_id] = generator
    generation_sessions[session_id] = {
        'account_name': account_name,
        'password_prefix': password_prefix,
        'region': region,
        'count': count,
        'threshold': threshold,
        'ghost_mode': use_ghost,
        'threads': threads_count,
        'start_time': datetime.now().isoformat(),
        'status': 'running',
        'generated': 0,
        'rare_found': 0,
        'couples_found': 0
    }
    
    return jsonify({
        'success': True,
        'session_id': session_id,
        'message': f'Generation started with {threads_count} threads',
        'threads': threads_count
    })

@app.route('/stream/<session_id>')
def stream_accounts(session_id):
    """Stream generated accounts as Server-Sent Events - FIXED VERSION"""
    def generate():
        generator = active_generations.get(session_id)
        session_info = generation_sessions.get(session_id)
        
        if not generator or not session_info:
            yield "data: {\"type\": \"error\", \"message\": \"Session not found\"}\n\n"
            return
        
        region = session_info['region']
        account_name = session_info['account_name']
        password_prefix = session_info['password_prefix']
        total_count = session_info['count']
        use_ghost = session_info['ghost_mode']
        threads_count = session_info['threads']
        
        # Send initial status
        yield f"data: {json.dumps({'type': 'status', 'message': f'Starting generation...', 'total': total_count, 'threads': threads_count})}\n\n"
        
        # Start generator
        generator.running = True
        generator.start_time = time.time()
        
        # Create thread pool
        executor = ThreadPoolExecutor(max_workers=threads_count)
        
        # Calculate accounts per thread
        accounts_per_thread = total_count // threads_count
        remaining_accounts = total_count % threads_count
        
        futures = []
        for thread_id in range(1, threads_count + 1):
            batch_size = accounts_per_thread + (1 if thread_id <= remaining_accounts else 0)
            if batch_size > 0:
                future = executor.submit(
                    generator.generate_accounts_batch,
                    region, account_name, password_prefix, batch_size, thread_id, use_ghost
                )
                futures.append(future)
        
        completed_accounts = 0
        all_results = []
        
        # Process completed futures
        for future in concurrent.futures.as_completed(futures):
            if not generator.running:
                break
            
            try:
                batch_results = future.result(timeout=300)
                
                for result in batch_results:
                    if not generator.running:
                        break
                    
                    if result:
                        completed_accounts += 1
                        session_info['generated'] = completed_accounts
                        session_info['rare_found'] = result['total_rare']
                        session_info['couples_found'] = result['total_couples']
                        
                        # Calculate speed
                        elapsed_time = time.time() - generator.start_time
                        speed = completed_accounts / elapsed_time if elapsed_time > 0 else 0
                        
                        # Add speed to result
                        result['speed'] = speed
                        result['total'] = total_count
                        
                        # Send account data
                        account_data = {
                            'type': 'account',
                            'count': completed_accounts,
                            'total': total_count,
                            'account': result['account'],
                            'is_rare': result['is_rare'],
                            'rarity_type': result['rarity_type'],
                            'rarity_score': result['rarity_score'],
                            'is_couple': result['is_couple'],
                            'total_rare': result['total_rare'],
                            'total_couples': result['total_couples'],
                            'thread_id': result.get('thread_id', 1),
                            'speed': speed
                        }
                        yield f"data: {json.dumps(account_data)}\n\n"
                        
                        # Send rare account notification
                        if result['is_rare']:
                            rare_data = {
                                'type': 'rare',
                                'message': f"🎯 RARE ACCOUNT FOUND!",
                                'details': f"Score: {result['rarity_score']} | Pattern: {result['rarity_type']}",
                                'account': result['account']
                            }
                            yield f"data: {json.dumps(rare_data)}\n\n"
                        
                        # Send couple notification
                        if result['is_couple']:
                            couple_data = {
                                'type': 'couple',
                                'message': f"💑 COUPLES ACCOUNT FOUND!",
                                'details': result['couple_reason'],
                                'account': result['account']
                            }
                            yield f"data: {json.dumps(couple_data)}\n\n"
                        
                        all_results.append(result)
                        
            except concurrent.futures.TimeoutError:
                yield f"data: {json.dumps({'type': 'error', 'message': 'Thread timeout'})}\n\n"
            except Exception as e:
                yield f"data: {json.dumps({'type': 'error', 'message': f'Thread error: {str(e)}'})}\n\n"
        
        # Generation complete
        executor.shutdown(wait=False)
        generator.running = False
        session_info['status'] = 'completed'
        session_info['end_time'] = datetime.now().isoformat()
        
        # Calculate final statistics
        elapsed_time = time.time() - generator.start_time
        speed = completed_accounts / elapsed_time if elapsed_time > 0 else 0
        
        # Create summary
        summary = {
            'type': 'complete',
            'message': 'Generation complete!',
            'summary': {
                'total_requested': total_count,
                'total_generated': completed_accounts,
                'rare_found': session_info['rare_found'],
                'couples_found': session_info['couples_found'],
                'threads_used': threads_count,
                'duration': elapsed_time,
                'speed': speed
            }
        }
        yield f"data: {json.dumps(summary)}\n\n"
        
    return Response(
        stream_with_context(generate()),
        mimetype='text/event-stream',
        headers={
            'Cache-Control': 'no-cache',
            'Connection': 'keep-alive',
            'X-Accel-Buffering': 'no'
        }
    )

@app.route('/stop/<session_id>')
def stop_generation(session_id):
    """Stop account generation"""
    generator = active_generations.get(session_id)
    if generator:
        generator.running = False
        if session_id in generation_sessions:
            generation_sessions[session_id]['status'] = 'stopped'
        return jsonify({'success': True, 'message': 'Generation stopped'})
    return jsonify({'success': False, 'message': 'Session not found'})

@app.route('/stats')
def get_stats():
    """Get generation statistics"""
    total_accounts = 0
    total_rare = 0
    total_couples = 0
    
    # Count accounts from files
    if os.path.exists(ACCOUNTS_FOLDER):
        for file in os.listdir(ACCOUNTS_FOLDER):
            if file.endswith('.json'):
                file_path = os.path.join(ACCOUNTS_FOLDER, file)
                try:
                    with open(file_path, 'r') as f:
                        accounts = json.load(f)
                        total_accounts += len(accounts)
                except:
                    continue
    
    # Count rare accounts
    if os.path.exists(RARE_ACCOUNTS_FOLDER):
        for file in os.listdir(RARE_ACCOUNTS_FOLDER):
            if file.endswith('.json'):
                file_path = os.path.join(RARE_ACCOUNTS_FOLDER, file)
                try:
                    with open(file_path, 'r') as f:
                        accounts = json.load(f)
                        total_rare += len(accounts)
                except:
                    continue
    
    # Count couples
    if os.path.exists(COUPLES_ACCOUNTS_FOLDER):
        for file in os.listdir(COUPLES_ACCOUNTS_FOLDER):
            if file.endswith('.json'):
                file_path = os.path.join(COUPLES_ACCOUNTS_FOLDER, file)
                try:
                    with open(file_path, 'r') as f:
                        couples = json.load(f)
                        total_couples += len(couples)
                except:
                    continue
    
    active_sessions = [s for s in generation_sessions.values() if s['status'] == 'running']
    
    return jsonify({
        'total_accounts': total_accounts,
        'total_rare': total_rare,
        'total_couples': total_couples,
        'rarity_threshold': RARITY_SCORE_THRESHOLD,
        'regions_available': len(REGION_LANG),
        'active_sessions': len(active_sessions),
        'max_threads': MAX_THREADS
    })

@app.route('/download/<filename>')
def download_file(filename):
    """Download generated files"""
    safe_filename = os.path.basename(filename)
    
    if safe_filename.endswith('.json'):
        folder = ACCOUNTS_FOLDER
        if 'rare' in safe_filename.lower():
            folder = RARE_ACCOUNTS_FOLDER
        elif 'couple' in safe_filename.lower():
            folder = COUPLES_ACCOUNTS_FOLDER
        
        file_path = os.path.join(folder, safe_filename)
        if os.path.exists(file_path):
            return send_file(file_path, as_attachment=True)
    
    return jsonify({'error': 'File not found'}), 404

if __name__ == '__main__':
    print("🌐 Free Fire RARE Account Generator Web Interface")
    print("================================================")
    print(f"📁 Base Folder: {BASE_FOLDER}")
    print(f"📊 Accounts: {ACCOUNTS_FOLDER}")
    print(f"💎 Rare: {RARE_ACCOUNTS_FOLDER}")
    print(f"💑 Couples: {COUPLES_ACCOUNTS_FOLDER}")
    print(f"🔐 Tokens: {TOKENS_FOLDER}")
    print(f"👻 GHOST: {GHOST_FOLDER}")
    print(f"🚀 Max Threads: {MAX_THREADS}")
    print(f"⏱️ Request Timeout: {REQUEST_TIMEOUT}s")
    print(f"⚠️ Safety Limit: 100 accounts per session")
    print("🌐 Web server starting on http://localhost:5000")
    
    # Force port 5000
    app.run(debug=True, host='0.0.0.0', port=5000, threaded=True)