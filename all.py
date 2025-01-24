#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
PDF Translation Script
Created: 2025-01-23 19:26:20
Author: x9ci
Version: 2.0.0

This script handles PDF translation with Arabic text support.
"""

from reportlab.lib.pagesizes import letter, A4
import pdfplumber
import pytesseract
from pdf2image import convert_from_path
from googletrans import Translator
import re
import logging
from PIL import Image, ImageFont, ImageDraw, ImageEnhance, ImageFilter
import os
from pathlib import Path
import shutil
from datetime import datetime
from typing import List, Dict, Optional, Union, Tuple, Any
from reportlab.pdfgen import canvas
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
import tempfile
from PyPDF2 import PdfReader, PdfWriter
from io import BytesIO
import arabic_reshaper
from bidi.algorithm import get_display
import sys
import time
import json
from tqdm import tqdm
import urllib.request
import logging.handlers
import threading
from concurrent.futures import ThreadPoolExecutor, as_completed
import requests
import hashlib
import atexit
from collections import defaultdict
import subprocess
from typing import Dict, List, Optional, Tuple
import argparse
from dataclasses import dataclass
import gc
# واردات المكونات المحلية
from arabic_handler import ArabicTextHandler # Add this line to import PDFHandler



class ConfigManager:
    """إدارة الإعدادات والتكوين"""
    
    def __init__(self):
        self.config_path = Path(__file__).parent / 'config.json'
        self.config = self.load_config()

    def load_config(self) -> dict:
        """تحميل إعدادات التكوين"""
        default_config = {
            'font_paths': [
                '/usr/share/fonts/truetype/fonts-arabeyes/ae_AlArabiya.ttf',
                '/usr/share/fonts/truetype/fonts-arabeyes/ae_Furat.ttf',
                '/usr/local/share/fonts/Amiri-Regular.ttf',
                './fonts/Amiri-Regular.ttf'
            ],
            'font_urls': {
                'Amiri-Regular.ttf': 'https://github.com/google/fonts/raw/main/ofl/amiri/Amiri-Regular.ttf',
                'ae_AlArabiya.ttf': 'https://github.com/fonts-arabeyes/ae_fonts/raw/master/ae_fonts_1.1/Fonts/TrueType/ae_AlArabiya.ttf'
            },
            'tesseract_config': {
                'lang': 'ara+eng',
                'config': '--psm 3'
            },
            'translation': {
                'batch_size': 10,
                'timeout': 30,
                'retries': 3
            },
            'output': {
                'dpi': 300,
                'quality': 95,
                'format': 'PDF'
            }
        }

        try:
            if self.config_path.exists():
                with open(self.config_path, 'r', encoding='utf-8') as f:
                    loaded_config = json.load(f)
                    # دمج الإعدادات المحملة مع الإعدادات الافتراضية
                    return {**default_config, **loaded_config}
            return default_config
        except Exception as e:
            logging.error(f"خطأ في تحميل ملف الإعدادات: {e}")
            return default_config

    def save_config(self) -> bool:
        """حفظ إعدادات التكوين"""
        try:
            with open(self.config_path, 'w', encoding='utf-8') as f:
                json.dump(self.config, f, ensure_ascii=False, indent=4)
            return True
        except Exception as e:
            logging.error(f"خطأ في حفظ ملف الإعدادات: {e}")
            return False

    def get(self, key: str, default: Any = None) -> Any:
        """الحصول على قيمة إعداد معين"""
        return self.config.get(key, default)

    def update(self, key: str, value: Any) -> bool:
        """تحديث قيمة إعداد معين"""
        try:
            self.config[key] = value
            return self.save_config()
        except Exception as e:
            logging.error(f"خطأ في تحديث الإعدادات: {e}")
            return False
        

class CacheManager:
    """إدارة التخزين المؤقت للترجمات"""
    
    def __init__(self):
        self.cache_dir = Path(__file__).parent / 'cache'
        self.cache_dir.mkdir(exist_ok=True)
        self.cache_file = self.cache_dir / 'translations.json'
        self.cache = self.load_cache()
        self.lock = threading.Lock()

    def load_cache(self) -> Dict[str, str]:
        """تحميل الترجمات المخزنة مؤقتاً"""
        try:
            if self.cache_file.exists():
                with open(self.cache_file, 'r', encoding='utf-8') as f:
                    return json.load(f)
            return {}
        except Exception as e:
            logging.error(f"خطأ في تحميل الذاكرة المؤقتة: {e}")
            return {}

    def save_cache(self) -> bool:
        """حفظ الترجمات في الذاكرة المؤقتة"""
        try:
            with self.lock:
                with open(self.cache_file, 'w', encoding='utf-8') as f:
                    json.dump(self.cache, f, ensure_ascii=False, indent=4)
            return True
        except Exception as e:
            logging.error(f"خطأ في حفظ الذاكرة المؤقتة: {e}")
            return False

    def get_translation(self, text: str) -> Optional[str]:
        """الحصول على ترجمة مخزنة"""
        text_hash = hashlib.md5(text.encode()).hexdigest()
        return self.cache.get(text_hash)

    def store_translation(self, text: str, translation: str) -> bool:
        """تخزين ترجمة جديدة"""
        try:
            with self.lock:
                text_hash = hashlib.md5(text.encode()).hexdigest()
                self.cache[text_hash] = translation
                return self.save_cache()
        except Exception as e:
            logging.error(f"خطأ في تخزين الترجمة: {e}")
            return False

    def clear_cache(self) -> bool:
        """مسح الذاكرة المؤقتة"""
        try:
            with self.lock:
                self.cache = {}
                return self.save_cache()
        except Exception as e:
            logging.error(f"خطأ في مسح الذاكرة المؤقتة: {e}")
            return False
        

class FontManager:
    """إدارة الخطوط وتحميلها"""
    
    def __init__(self, config_manager: ConfigManager):
        self.logger = logging.getLogger(__name__)
        self.config = config_manager
        self.font_name: str = "ArabicFont"
        self.loaded_fonts: List[str] = []
        self.base_path = Path(__file__).parent
        self.fonts_dir = self.base_path / "fonts"
        self.fonts_dir.mkdir(exist_ok=True)
        self._setup_fonts()

    def _setup_fonts(self) -> None:
        """إعداد وتهيئة الخطوط الأولية"""
        self.font_paths = self.config.get('font_paths', [])
        self.font_urls = self.config.get('font_urls', {})
        self.register_default_fonts()

    def register_default_fonts(self) -> None:
        """تسجيل الخطوط الافتراضية"""
        default_fonts = [
            ('Helvetica', 'Helvetica'),
            ('Helvetica-Bold', 'Helvetica-Bold'),
            ('Times-Roman', 'Times-Roman'),
            ('Times-Bold', 'Times-Bold')
        ]
        for font_name, font_path in default_fonts:
            if font_name not in pdfmetrics.getRegisteredFontNames():
                try:
                    pdfmetrics.registerFont(TTFont(font_name, font_path))
                except Exception as e:
                    self.logger.warning(f"فشل تسجيل الخط {font_name}: {e}")

    def check_font_paths(self) -> List[str]:
        """التحقق من مسارات الخطوط المتوفرة"""
        possible_font_dirs = [
            Path("/usr/share/fonts"),
            Path("/usr/local/share/fonts"),
            Path.home() / ".fonts",
            Path.home() / "Library/Fonts",  # MacOS
            Path("C:\\Windows\\Fonts"),  # Windows
            self.fonts_dir
        ]
        
        found_fonts: List[str] = []
        arab_keywords = ['arab', 'amiri', 'noto', 'freesans']
        
        self.logger.info("جاري البحث عن الخطوط المتوفرة...")
        for font_dir in possible_font_dirs:
            if font_dir.exists():
                self.logger.info(f"البحث في المجلد: {font_dir}")
                for font_path in font_dir.rglob("*.[to][tt][ff]"):
                    if any(kw in font_path.name.lower() for kw in arab_keywords):
                        found_fonts.append(str(font_path))
                        self.logger.info(f"تم العثور على خط: {font_path}")
        
        return found_fonts

    def download_font(self, font_name: str, url: str) -> bool:
        """تحميل خط من الإنترنت"""
        try:
            font_path = self.fonts_dir / font_name
            self.logger.info(f"جاري تحميل الخط {font_name}...")
            
            response = requests.get(url, stream=True)
            response.raise_for_status()
            
            total_size = int(response.headers.get('content-length', 0))
            block_size = 1024
            progress_bar = tqdm(
                total=total_size,
                unit='iB',
                unit_scale=True,
                desc=f"تحميل {font_name}"
            )
            
            with open(font_path, 'wb') as f:
                for data in response.iter_content(block_size):
                    progress_bar.update(len(data))
                    f.write(data)
            
            progress_bar.close()
            self.logger.info(f"تم تحميل الخط بنجاح: {font_path}")
            return True
            
        except Exception as e:
            self.logger.error(f"خطأ في تحميل الخط {font_name}: {e}")
            return False

    def load_font(self, font_path: str) -> bool:
        """تحميل خط معين"""
        try:
            font_name = f"Arabic_{Path(font_path).stem}"
            if font_name not in pdfmetrics.getRegisteredFontNames():
                pdfmetrics.registerFont(TTFont(font_name, font_path))
                self.loaded_fonts.append(font_path)
                self.logger.info(f"تم تحميل الخط: {font_path}")
                return True
            return True
        except Exception as e:
            self.logger.warning(f"فشل تحميل الخط {font_path}: {str(e)}")
            return False

    def initialize_fonts(self) -> bool:
        """تهيئة الخطوط العربية"""
        try:
            # محاولة تحميل الخطوط المحلية
            for font_path in self.font_paths:
                if Path(font_path).exists():
                    if self.load_font(font_path):
                        return True

            # محاولة تحميل الخطوط من الإنترنت إذا لم تتوفر محلياً
            if not self.loaded_fonts:
                self.logger.warning("لم يتم العثور على خطوط محلية. جاري التحميل من الإنترنت...")
                for font_name, url in self.font_urls.items():
                    if self.download_font(font_name, url):
                        font_path = self.fonts_dir / font_name
                        if self.load_font(str(font_path)):
                            return True

            return bool(self.loaded_fonts)

        except Exception as e:
            self.logger.error(f"خطأ في تهيئة الخطوط: {str(e)}")
            return False

    def get_arabic_font(self) -> Optional[str]:
        """الحصول على مسار الخط العربي المحمل"""
        return next(iter(self.loaded_fonts), None)
    

class ConfigManager:
class CacheManager:

class FontManager:
class TextExtractor:
class TranslationProcessor:
class PDFProcessor:
class PDFTranslator:
class PDFTextProcessor:
class ChessNotationProcessor:
class PDFRenderer:
class PDFImageProcessor:
class PDFSecurityHandler:
class PDFMetadataProcessor:
class PDFOptimizer:
class OCRProcessor:
class TextLayoutAnalyzer:
class ArabicTextProcessor:
class PDFStats:
class PDFOptimizer:
class PageProcessor:
class PDFHandler:
class TextProcessor:
