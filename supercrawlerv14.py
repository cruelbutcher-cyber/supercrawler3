import streamlit as st
import requests
from bs4 import BeautifulSoup, FeatureNotFound
from urllib.parse import urljoin, urlparse, parse_qs, unquote, quote, urlunparse
from collections import deque
import csv
import datetime
import re
import time
from io import StringIO
import json
import hashlib
import html
import logging
import tldextract
from urllib3.util import Retry
from requests.adapters import HTTPAdapter

class EnhancedWebCrawler:
    def __init__(self, start_url, crawl_mode="Standard"):
        self.session = self._create_session()
        self.start_url = start_url
        self.keywords = ["gowithguide", "go with guide", "go-with-guide", "87121"]
        self.main_domain = urlparse(start_url).netloc
        self.crawl_mode = crawl_mode
        self.max_pages = {"Quick": 5, "Standard": 150, "Complete": 5000}[crawl_mode]
        self.visited = set()
        self.results = []
        self.queue = deque([start_url])
        self.categories = []
        self.current_category = None
        self.status_messages = []
        self.user_stopped = False
        self.pages_crawled = 0
        self.redirect_cache = {}
        self.internal_links = set()
        self.known_shorteners = [
            'bit.ly', 'tinyurl.com', 'goo.gl', 't.co', 'ow.ly', 'is.gd', 
            'buff.ly', 'adf.ly', 'bit.do', 'mcaf.ee', 'su.pr', 'tiny.cc',
            'tidd.ly', 'redirectingat.com', 'go.redirectingat.com', 'go.skimresources.com'
        ]
        self.awin_domains = ['awin1.com', 'zenaps.com']
        self.potential_affiliate_domains = [
            'track.', 'go.', 'click.', 'buy.', 'shop.', 'link.', 'visit.', 
            'affiliate.', 'partners.', 'tracking.', 'redirect.', 'ref.'
        ]
        self.crawled_pages_content = {}
        self.url_fragments_checked = set()
        self.setup_logger()

    def setup_logger(self):
        self.logger = logging.getLogger('crawler')
        self.logger.setLevel(logging.INFO)
        if not self.logger.handlers:
            handler = logging.StreamHandler()
            formatter = logging.Formatter('%(asctime)s - %(levelname)s - %(message)s')
            handler.setFormatter(formatter)
            self.logger.addHandler(handler)

    def _create_session(self):
        session = requests.Session()
        retries = Retry(
            total=3,
            backoff_factor=0.5,
            status_forcelist=[429, 500, 502, 503, 504],
            allowed_methods=["GET", "HEAD"]
        )
        adapter = HTTPAdapter(max_retries=retries)
        session.mount("http://", adapter)
        session.mount("https://", adapter)
        session.headers.update({
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36',
            'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,*/*;q=0.8',
            'Accept-Language': 'en-US,en;q=0.5',
            'Connection': 'keep-alive',
            'Upgrade-Insecure-Requests': '1',
            'Cache-Control': 'max-age=0'
        })
        return session
    def get_soup(self, html_content):
        try:
            return BeautifulSoup(html_content, 'lxml')
        except FeatureNotFound:
            self.status_messages.append("Warning: 'lxml' parser not found. Using 'html.parser' instead.")
            return BeautifulSoup(html_content, 'html.parser')

    def is_same_domain(self, url):
        main_domain_parts = tldextract.extract(self.start_url)
        url_domain_parts = tldextract.extract(url)
        return (main_domain_parts.domain == url_domain_parts.domain and 
                main_domain_parts.suffix == url_domain_parts.suffix)

    def is_subdomain_of(self, url_netloc):
        main_domain = self.main_domain.replace("www.", "").lower()
        url_netloc = url_netloc.replace("www.", "").lower()
        return url_netloc.endswith("." + main_domain) or url_netloc == main_domain

    def is_relevant_path(self, url):
        parsed_url = urlparse(url)
        path = parsed_url.path.lower()
        if re.search(r'\.(jpg|jpeg|png|gif|svg|pdf|zip|rar|css|js|xml|json)$', path):
            return False
        if re.search(r'/(login|logout|register|signin|signout|cart|checkout|privacy|terms)/?$', path):
            return False
        if re.search(r'/(post|article|blog|news|story|travel|guide|destination|affiliate)/', path):
            return True
        if len(parse_qs(parsed_url.query)) > 3:
            return False
        return True

    def normalize_url(self, url):
        parsed = urlparse(url)
        normalized = urlunparse((parsed.scheme, parsed.netloc, parsed.path, 
                                parsed.params, parsed.query, ''))
        if normalized.endswith('/'):
            normalized = normalized[:-1]
        return normalized

    def looks_like_affiliate_url(self, url):
        url_lower = url.lower()
        parsed_url = urlparse(url_lower)
        netloc = parsed_url.netloc
        if any(shortener in netloc for shortener in self.known_shorteners):
            return True
        if any(tracker in netloc for tracker in self.potential_affiliate_domains):
            return True
        if any(domain in netloc for domain in self.awin_domains) and '87121' in url_lower:
            return True
        query_params = parse_qs(parsed_url.query)
        affiliate_params = ['aff', 'affid', 'affiliateid', 'ref', 'refid', 'referral', 
                           'referralid', 'partner', 'partnerId', 'utm_source']
        for param in affiliate_params:
            if param in query_params:
                return True
        tracking_params = ['utm_', 'ref', 'aff', 'source', 'campaign', 'medium']
        tracking_count = sum(1 for param in query_params if any(t in param for t in tracking_params))
        if tracking_count >= 2:
            return True
        return False
    def extract_redirection_url(self, html_content, url):
        soup = self.get_soup(html_content)
        redirect_urls = []
        meta_refresh = soup.find('meta', attrs={'http-equiv': re.compile('^refresh$', re.I)})
        if meta_refresh and meta_refresh.get('content'):
            match = re.search(r'url=(.+)', meta_refresh['content'], re.I)
            if match:
                redirect_url = match.group(1).strip()
                redirect_urls.append(urljoin(url, redirect_url))
        script_patterns = [
            r'window\.location(?:\.href)?\s*=\s*[\'"](.+?)[\'"]',
            r'window\.location\.replace\([\'"](.+?)[\'"]\)',
            r'window\.open\([\'"](.+?)[\'"]\)',
            r'location\.href\s*=\s*[\'"](.+?)[\'"]',
            r'location\.replace\([\'"](.+?)[\'"]\)',
            r'setTimeout\([\'"]window\.location\.href=[\'"](.+?)[\'"][\'"]',
            r'url:\s*[\'"](.+?)[\'"]',
            r'href=[\'"](.+?)[\'"]'
        ]
        scripts = soup.find_all('script')
        for script in scripts:
            if script.string:
                for pattern in script_patterns:
                    matches = re.findall(pattern, script.string)
                    for match in matches:
                        if len(match) > 10:
                            redirect_urls.append(urljoin(url, match))
        parsed_url = urlparse(url)
        query_params = parse_qs(parsed_url.query)
        redirect_params = ['redirect_to', 'redirect', 'url', 'link', 'goto', 'target', 'ued']
        for param in redirect_params:
            if param in query_params:
                decoded_url = unquote(query_params[param][0])
                redirect_urls.append(urljoin(url, decoded_url))
        return redirect_urls

    def check_url_for_keywords(self, url, source_url):
        if not url or not isinstance(url, str):
            return
        url_hash = hashlib.md5(url.encode()).hexdigest()
        if url_hash in self.url_fragments_checked:
            return
        self.url_fragments_checked.add(url_hash)
        matched_kws = self.get_matched_keywords(url)
        if matched_kws:
            self.add_result(
                source_url=source_url,
                matched_url=url,
                element='url',
                attribute='href',
                content=url,
                keywords=matched_kws,
                location_type='direct_url'
            )
        if self.looks_like_affiliate_url(url):
            final_url, history = self.resolve_redirects(url)
            if final_url != url:
                matched_kws_final = self.get_matched_keywords(final_url)
                if matched_kws_final:
                    self.add_result(
                        source_url=source_url,
                        matched_url=final_url,
                        element='url',
                        attribute='href',
                        content=f"Redirected from: {url} to: {final_url}",
                        keywords=matched_kws_final,
                        location_type='redirected_url'
                    )
                elif any(domain in final_url for domain in self.awin_domains):
                    parsed = urlparse(final_url)
                    params = parse_qs(parsed.query)
                    awin_mid = params.get('awinmid', [None])[0] or params.get('v', [None])[0]
                    if awin_mid == '87121':
                        self.add_result(
                            source_url=source_url,
                            matched_url=final_url,
                            element='url',
                            attribute='href',
                            content=f"AWIN link with merchant ID 87121: {final_url}",
                            keywords=['87121'],
                            location_type='awin_affiliate_url'
                        )
            for intermediate_url in history:
                matched_kws_intermediate = self.get_matched_keywords(intermediate_url)
                if matched_kws_intermediate:
                    self.add_result(
                        source_url=source_url,
                        matched_url=intermediate_url,
                        element='url',
                        attribute='href',
                        content=f"Redirect chain URL: {intermediate_url}",
                        keywords=matched_kws_intermediate,
                        location_type='redirect_chain_url'
                    )
                elif any(domain in intermediate_url for domain in self.awin_domains):
                    parsed = urlparse(intermediate_url)
                    params = parse_qs(parsed.query)
                    if params.get('awinmid', [None])[0] == '87121':
                        self.add_result(
                            source_url=source_url,
                            matched_url=intermediate_url,
                            element='url',
                            attribute='href',
                            content=f"AWIN redirect link with merchant ID 87121: {intermediate_url}",
                            keywords=['87121'],
                            location_type='awin_affiliate_redirect'
                        )

    def process_url(self, url):
        if url in self.visited or self.pages_crawled >= self.max_pages or not url:
            return []
        self.visited.add(url)
        self.pages_crawled += 1
        try:
            response = self.session.get(
                url, 
                headers={
                    'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36',
                    'Accept': 'text/html,application/xhtml+xml,application/xml'
                }, 
                timeout=20, 
                allow_redirects=True
            )
            response.raise_for_status()
        except Exception as e:
            self.status_messages.append(f"Error fetching {url}: {str(e)}")
            return []
        content_type = response.headers.get('Content-Type', '').lower()
        if 'text/html' not in content_type and 'application/xhtml+xml' not in content_type:
            return []
        final_url = response.url
        html_content = response.text
        self.crawled_pages_content[final_url] = html_content
        soup = self.get_soup(html_content)  
        js_redirects = self.extract_redirection_url(html_content, final_url)
        for js_redirect in js_redirects:
            self.check_url_for_keywords(js_redirect, final_url)
        elements = soup.find_all([
            'a', 'div', 'section', 'title', 'main', 
            'article', 'span', 'p', 'img', 'meta', 
            'iframe', 'script', 'button', 'form'
        ])
        internal_urls = []
        for element in elements:
            urls = self.check_element(element, final_url)
            internal_urls.extend(urls)
        script_tags = soup.find_all('script')
        for script in script_tags:
            if script.string:
                urls_in_js = re.findall(r'(https?://[^\s\'"]+)', script.string)
                for js_url in urls_in_js:
                    js_url = re.sub(r'["\')]$', '', js_url)
                    self.check_url_for_keywords(js_url, final_url)
                    parsed_js_url = urlparse(js_url)
                    if self.is_subdomain_of(parsed_js_url.netloc):
                        internal_urls.append(js_url)
                json_patterns = [
                    r'["\']?(?:url|href|link)["\']?\s*:\s*["\']?(https?://[^\s\'"]+)["\']?',
                    r'window\.location\s*=\s*["\']?(https?://[^\s\'"]+)["\']?',
                    r'["\']?(?:redirectUrl|redirect_url|redirectLink)["\']?\s*:\s*["\']?(https?://[^\s\'"]+)["\']?',
                    r'["\']?(?:affiliateUrl|affiliate_url|partnerUrl)["\']?\s*:\s*["\']?(https?://[^\s\'"]+)["\']?'
                ]
                for pattern in json_patterns:
                    matches = re.findall(pattern, script.string)
                    for match in matches:
                        match = re.sub(r'["\')]$', '', match)
                        self.check_url_for_keywords(match, final_url)
                        if self.is_subdomain_of(urlparse(match).netloc):
                            internal_urls.append(match)
        for element in soup.find_all(attrs=re.compile(r"^data-.*")):
            for attr_name, attr_value in element.attrs.items():
                if attr_name.startswith('data-') and isinstance(attr_value, str):
                    if ('url' in attr_name.lower() or 'link' in attr_name.lower() or 
                        'href' in attr_name.lower() or 'src' in attr_name.lower()):
                        if attr_value.startswith(('http://', 'https://', '//')):
                            full_url = urljoin(final_url, attr_value)
                            self.check_url_for_keywords(full_url, final_url)
                            if self.is_subdomain_of(urlparse(full_url).netloc):
                                internal_urls.append(full_url)
        for script in soup.find_all('script', {'type': 'application/ld+json'}):
            if script.string:
                try:
                    json_data = json.loads(script.string)
                    self._extract_urls_from_json(json_data, final_url, internal_urls)
                except json.JSONDecodeError:
                    pass
        filtered_internal_urls = []
        seen_urls = set()
        for url in internal_urls:
            normalized_url = self.normalize_url(url)
            if normalized_url not in seen_urls and normalized_url not in self.visited:
                seen_urls.add(normalized_url)
                if self.is_relevant_path(normalized_url):
                    filtered_internal_urls.append(url)
        return filtered_internal_urls

    def _extract_urls_from_json(self, json_data, base_url, url_list):
        if isinstance(json_data, dict):
            for key, value in json_data.items():
                if key.lower() in ('url', 'link', 'href', 'src') and isinstance(value, str):
                    if value.startswith(('http', '/')):
                        full_url = urljoin(base_url, value)
                        self.check_url_for_keywords(full_url, base_url)
                        if self.is_subdomain_of(urlparse(full_url).netloc):
                            url_list.append(full_url)
                else:
                    self._extract_urls_from_json(value, base_url, url_list)
        elif isinstance(json_data, list):
            for item in json_data:
                self._extract_urls_from_json(item, base_url, url_list)

    def check_element(self, element, source_url):
        internal_urls = []
        element_type = element.name if element.name else 'unknown'
        if element.name == 'a':
            if element.has_attr('href'):
                href = element['href'].strip()
                if href and not href.startswith(('javascript:', 'mailto:', 'tel:')):
                    resolved_url = urljoin(source_url, href)
                    self.check_url_for_keywords(resolved_url, source_url)
                    text = element.get_text(separator=' ', strip=True)
                    matched_kws = self.get_matched_keywords(text)
                    if matched_kws:
                        self.add_result(
                            source_url=source_url,
                            matched_url=resolved_url,
                            element=element_type,
                            attribute='text',
                            content=text,
                            keywords=matched_kws,
                            location_type='anchor_text'
                        )
                    parsed_url = urlparse(resolved_url)
                    if self.is_subdomain_of(parsed_url.netloc):
                        internal_urls.append(resolved_url)
            img = element.find('img')
            if img:
                if img.get('alt'):
                    alt_text = img['alt'].strip()
                    matched_kws = self.get_matched_keywords(alt_text)
                    if matched_kws and element.has_attr('href'):
                        resolved_url = urljoin(source_url, element['href'].strip())
                        self.add_result(
                            source_url=source_url,
                            matched_url=resolved_url,
                            element='a',
                            attribute='img_alt',
                            content=alt_text,
                            keywords=matched_kws,
                            location_type='image_banner'
                        )
                if img.get('title'):
                    title_text = img['title'].strip()
                    matched_kws = self.get_matched_keywords(title_text)
                    if matched_kws and element.has_attr('href'):
                        resolved_url = urljoin(source_url, element['href'].strip())
                        self.add_result(
                            source_url=source_url,
                            matched_url=resolved_url,
                            element='a',
                            attribute='img_title',
                            content=title_text,
                            keywords=matched_kws,
                            location_type='image_banner'
                        )
                if img.get('src'):
                    img_src = img['src'].strip()
                    if self.looks_like_affiliate_url(img_src):
                        img_url = urljoin(source_url, img_src)
                        self.check_url_for_keywords(img_url, source_url)
            for onclick_url in self.extract_urls_from_onclick(element, source_url):
                self.check_url_for_keywords(onclick_url, source_url)
                parsed_onclick_url = urlparse(onclick_url)
                if self.is_subdomain_of(parsed_onclick_url.netloc):
                    internal_urls.append(onclick_url)
            for attr_name, attr_val in element.attrs.items():
                if attr_name.startswith('data-') and isinstance(attr_val, str):
                    if ('url' in attr_name or 'link' in attr_name or 'href' in attr_name):
                        if attr_val.startswith(('http', '/')):
                            data_url = urljoin(source_url, attr_val)
                            self.check_url_for_keywords(data_url, source_url)
                            if self.is_subdomain_of(urlparse(data_url).netloc):
                                internal_urls.append(data_url)
        if element.name in ['p', 'div', 'span', 'title', 'h1', 'h2', 'h3', 'h4', 'h5', 'h6']:
            text = element.get_text(separator=' ', strip=True)
            matched_kws = self.get_matched_keywords(text)
            if matched_kws:
                self.add_result(
                    source_url=source_url,
                    matched_url=source_url,
                    element=element_type,
                    attribute='text',
                    content=text,
                    keywords=matched_kws,
                    location_type='content'
                )
            url_matches = re.findall(r'https?://[^\s\'"<>]+', text)
            for url_match in url_matches:
                url_match = re.sub(r'[,.:;!?)]$', '', url_match)
                self.check_url_for_keywords(url_match, source_url)
        if element.name == 'meta' and element.get('content'):
            content = element['content'].strip()
            matched_kws = self.get_matched_keywords(content)
            if matched_kws:
                attr_name = element.get('name') or element.get('property') or 'meta'
                self.add_result(
                    source_url=source_url,
                    matched_url=source_url,
                    element=element_type,
                    attribute=attr_name,
                    content=content,
                    keywords=matched_kws,
                    location_type='meta'
                )
            if ('url' in element.get('name', '').lower() or 
                'url' in element.get('property', '').lower()):
                if content.startswith(('http', '/')):
                    meta_url = urljoin(source_url, content)
                    self.check_url_for_keywords(meta_url, source_url)
                    if self.is_subdomain_of(urlparse(meta_url).netloc):
                        internal_urls.append(meta_url)
        if element.name == 'img':
            if element.get('alt'):
                alt_text = element['alt'].strip()
                matched_kws = self.get_matched_keywords(alt_text)
                if matched_kws:
                    self.add_result(
                        source_url=source_url,
                        matched_url=source_url,
                        element=element_type,
                        attribute='alt',
                        content=alt_text,
                        keywords=matched_kws,
                        location_type='alt_text'
                    )
            if element.get('title'):
                title_text = element['title'].strip()
                matched_kws = self.get_matched_keywords(title_text)
                if matched_kws:
                    self.add_result(
                        source_url=source_url,
                        matched_url=source_url,
                        element=element_type,
                        attribute='title',
                        content=title_text,
                        keywords=matched_kws,
                        location_type='title_text'
                    )
        if element.name == 'iframe' and element.get('src'):
            iframe_src = element['src'].strip()
            if iframe_src.startswith(('http', '//')):
                iframe_url = urljoin(source_url, iframe_src)
                self.check_url_for_keywords(iframe_url, source_url)
        if element.name == 'button':
            for onclick_url in self.extract_urls_from_onclick(element, source_url):
                self.check_url_for_keywords(onclick_url, source_url)
            button_text = element.get_text(separator=' ', strip=True)
            matched_kws = self.get_matched_keywords(button_text)
            if matched_kws:
                self.add_result(
                    source_url=source_url,
                    matched_url=source_url,
                    element=element_type,
                    attribute='text',
                    content=button_text,
                    keywords=matched_kws,
                    location_type='button_text'
                )
        for attr in element.attrs:
            if attr.startswith('data-') and isinstance(element[attr], str):
                attr_value = element[attr].strip()
                if ('url' in attr.lower() or 'href' in attr.lower() or 'link' in attr.lower()):
                    if attr_value and attr_value.startswith(('http', '//')):
                        data_url = urljoin(source_url, attr_value)
                        self.check_url_for_keywords(data_url, source_url)
                        if self.is_subdomain_of(urlparse(data_url).netloc):
                            internal_urls.append(data_url)
                matched_kws = self.get_matched_keywords(attr_value)
                if matched_kws:
                    self.add_result(
                        source_url=source_url,
                        matched_url=source_url,
                        element=element_type,
                        attribute=attr,
                        content=attr_value,
                        keywords=matched_kws,
                        location_type='data_attribute'
                    )
        return internal_urls

    def add_result(self, source_url, matched_url, element, attribute, content, keywords, location_type):
        for keyword in keywords:
            match_id = hashlib.md5(f"{matched_url}:{element}:{attribute}:{keyword}:{location_type}".encode()).hexdigest()
            if any(result.get('match_id') == match_id for result in self.results):
                continue
            result = {
                'source_url': source_url,
                'matched_url': matched_url,
                'element': element,
                'attribute': attribute,
                'keyword': keyword,
                'content': content[:500] if content else '',
                'location_type': location_type,
                'timestamp': datetime.datetime.now().isoformat(),
                'match_id': match_id
            }
            self.results.append(result)
            self.logger.info(f"Found affiliate link: {matched_url} (keyword: {keyword})")
    def extract_categories(self):
        try:
            response = self.session.get(self.start_url)
            soup = self.get_soup(response.text)  
            categories = []
            category_priority = [
                'travel', 'blog', 'resources', 'guides', 'destinations',
                'tours', 'activities', 'affiliate', 'partner', 'reviews',
                'articles', 'news', 'features', 'stories'
            ]
            nav_elements = soup.find_all(['nav', 'ul', 'div'], class_=lambda c: c and any$$term in c.lower() for term in ['nav', 'menu', 'categories', 'main-menu']$$)
            for nav in nav_elements:
                for link in nav.find_all('a', href=True):
                    href = link['href'].lower()
                    text = link.get_text().lower().strip()
                    if not href or href.startswith('#'):
                        continue
                    if any(term in href for term in ['/cart', '/login', '/register', '/account']):
                        continue
                    full_url = urljoin(self.start_url, href)
                    if not self.is_same_domain(full_url):
                        continue
                    cat_name = None
                    cat_match = re.search(r'/(?:category|topics|sections?|tags?)/([^/]+)', href)
                    if cat_match:
                        cat_name = cat_match.group(1).lower()
                    else:
                        for cat in category_priority:
                            if cat in href or cat in text:
                                cat_name = cat
                                break
                    if not cat_name:
                        if 3 <= len(text) <= 20 and ' ' not in text:
                            cat_name = text
                        else:
                            path_parts = urlparse(full_url).path.strip('/').split('/')
                            if path_parts:
                                cat_name = path_parts[-1].lower()
                            else:
                                cat_name = 'other'
                    categories.append((cat_name, full_url))
            sorted_categories = []
            for cat in category_priority:
                matched = [c for c in categories if c[0] == cat]
                if matched:
                    sorted_categories.append(matched[0])
            remaining = [c for c in categories if c[0] not in [sc[0] for sc in sorted_categories]]
            sorted_categories.extend(remaining)
            unique_cat_urls = set()
            unique_categories = []
            for cat_name, cat_url in sorted_categories:
                if cat_url not in unique_cat_urls:
                    unique_cat_urls.add(cat_url)
                    unique_categories.append((cat_name, cat_url))
                    if len(unique_categories) >= 10:
                        break
            return unique_categories
        except Exception as e:
            self.status_messages.append(f"Error extracting categories: {str(e)}")
            return []

    def get_main_pages(self):
        try:
            response = self.session.get(self.start_url)
            soup = self.get_soup(response.text)  
            main_links = []
            seen_urls = set()
            content_patterns = [
                r'/(?:post|article|blog|story|guide)s?/',
                r'/(?:travel|destination|tour)s?/',
                r'/(?:partner|affiliate)s?/',
                r'/(?:review|resource)s?/'
            ]
            priority_terms = [
                'affiliate', 'partner', 'sponsor', 'advertis', 
                'review', 'guid', 'tour', 'travel', 'destination', 'blog'
            ]
            all_links = []
            for link in soup.find_all('a', href=True):
                href = link['href'].strip()
                if not href or href.startswith(('#', 'javascript:', 'mailto:', 'tel:')):
                    continue
                url = urljoin(self.start_url, href)
                if not self.is_same_domain(url):
                    continue
                if re.search(r'\.(jpg|jpeg|png|gif|pdf|zip|doc|docx)$', url, re.I):
                    continue
                text = link.get_text().strip().lower()
                priority = 0
                for pattern in content_patterns:
                    if re.search(pattern, url, re.I):
                        priority += 3
                for term in priority_terms:
                    if term in url.lower() or term in text:
                        priority += 2
                parent = link.find_parent(['article', 'section', 'main'])
                if parent:
                    priority += 1
                all_links.append((url, priority))
            all_links.sort(key=lambda x: x[1], reverse=True)
            for url, _ in all_links:
                normalized_url = self.normalize_url(url)
                if normalized_url not in seen_urls and self.is_relevant_path(normalized_url):
                    seen_urls.add(normalized_url)
                    main_links.append(url)
                    if len(main_links) >= self.max_pages:
                        break
            return main_links
        except Exception as e:
            self.status_messages.append(f"Error getting main pages: {str(e)}")
            return []

    def get_category_pages(self, category_url):
        try:
            response = self.session.get(category_url)
            soup = self.get_soup(response.text)  
            article_links = []
            seen_urls = set()
            article_elements = soup.find_all(['article', 'div', 'section', 'li'], class_=lambda c: c and any$$term in (c.lower() if c else '') for term in ['post', 'article', 'entry', 'item', 'card', 'stories']$$)
            if article_elements:
                for container in article_elements:
                    links = container.find_all('a', href=True)
                    for link in links:
                        url = urljoin(category_url, link['href'].strip())
                        if not self.is_same_domain(url) or not self.is_relevant_path(url):
                            continue
                        normalized_url = self.normalize_url(url)
                        if normalized_url not in seen_urls:
                            seen_urls.add(normalized_url)
                            article_links.append(url)
            if len(article_links) < self.max_pages:
                for link in soup.find_all('a', href=True):
                    url = urljoin(category_url, link['href'].strip())
                    normalized_url = self.normalize_url(url)
                    if normalized_url in seen_urls:
                        continue
                    if not self.is_same_domain(url) or not self.is_relevant_path(url):
                        continue
                    if (re.search(r'/(?:article|post|blog|news|story|guide)/', url) or
                        re.search(r'/\d{4}/\d{2}/', url)):
                        seen_urls.add(normalized_url)
                        article_links.append(url)
                        if len(article_links) >= self.max_pages:
                            break
            pagination_patterns = [
                r'next', r'more', r'page[-_]\d+', r'p=\d+', r'page=\d+'
            ]
            for link in soup.find_all('a', href=True):
                href = link['href'].lower()
                text = link.get_text().lower().strip()
                if any(re.search(pat, href) or re.search(pat, text) for pat in pagination_patterns):
                    url = urljoin(category_url, link['href'])
                    normalized_url = self.normalize_url(url)
                    if normalized_url not in seen_urls and self.is_same_domain(url):
                        seen_urls.add(normalized_url)
                        article_links.append(url)
                        if len(article_links) >= self.max_pages:
                            break
            try:
                date_sorted_links = []
                for url in article_links:
                    date_match = re.search(r'/(\d{4})/(\d{2})/', url)
                    if date_match:
                        year, month = date_match.groups()
                        date_sorted_links.append((url, (int(year), int(month))))
                if date_sorted_links:
                    date_sorted_links.sort(key=lambda x: x[1], reverse=True)
                    article_links = [url for url, _ in date_sorted_links]
            except Exception:
                pass
            return article_links[:self.max_pages]
        except Exception as e:
            self.status_messages.append(f"Error getting category pages: {str(e)}")
            return []

    def resolve_redirects(self, url, depth=0, max_depth=5):
        if depth > max_depth:
            return url, []
        if url in self.redirect_cache:
            return self.redirect_cache[url]
        try:
            parsed = urlparse(url)
            if parsed.scheme not in ('http', 'https'):
                return url, []
            is_shortener = any(domain in parsed.netloc for domain in self.known_shorteners)
            if is_shortener or self.looks_like_affiliate_url(url):
                response = self.session.get(
                    url, 
                    allow_redirects=False,
                    timeout=15,
                    headers={
                        'User-Agent': 'Mozilla/5.0',
                        'Accept': 'text/html,application/xhtml+xml'
                    }
                )
                history = []
                if 300 <= response.status_code < 400:
                    location = response.headers.get('Location', '')
                    if location:
                        redirect_url = urljoin(url, location)
                        final_url, redirect_history = self.resolve_redirects(redirect_url, depth + 1, max_depth)
                        history = [url] + redirect_history
                        self.redirect_cache[url] = (final_url, history)
                        return final_url, history
                if 'text/html' in response.headers.get('Content-Type', ''):
                    potential_redirects = self.extract_redirection_url(response.text, url)
                    if potential_redirects:
                        redirect_url = potential_redirects[0]
                        final_url, redirect_history = self.resolve_redirects(redirect_url, depth + 1, max_depth)
                        history = [url] + redirect_history
                        self.redirect_cache[url] = (final_url, history)
                        return final_url, history
                final_url = response.url if 'Location' not in response.headers else url
                self.redirect_cache[url] = (final_url, history)
                return final_url, history
            else:
                response = self.session.head(
                    url, 
                    allow_redirects=True, 
                    timeout=10
                )
                final_url = response.url
                history = [r.url for r in response.history]
                self.redirect_cache[url] = (final_url, history)
                return final_url, history
        except Exception as e:
            self.status_messages.append(f"Error resolving redirects for {url}: {str(e)}")
            return url, []

    def get_matched_keywords(self, text):
        if not isinstance(text, str) or not text.strip():
            return []
        text_lower = text.lower().strip()
        exact_matches = []
        for kw in self.keywords:
            kw_lower = kw.lower()
            pattern = rf'(?:^|\s|[-_/=&]){re.escape(kw_lower)}(?:$|\s|[-_/=&])'
            if re.search(pattern, text_lower):
                exact_matches.append(kw)
            kw_encoded = kw.replace(' ', '%20')
            pattern_encoded = rf'(?:^|\s|[-_/=&]){re.escape(kw_encoded)}(?:$|\s|[-_/=&])'
            if re.search(pattern_encoded, text_lower):
                exact_matches.append(kw)
            kw_plus_encoded = kw.replace(' ', '+')
            pattern_plus_encoded = rf'(?:^|\s|[-_/=&]){re.escape(kw_plus_encoded)}(?:$|\s|[-_/=&])'
            if re.search(pattern_plus_encoded, text_lower):
                exact_matches.append(kw)
        url_patterns = [
            r'(?:https?://)?(?:www\.)?gowithguide\.com',
            r'utm_source=([^&]*)',
            r'utm_campaign=([^&]*)',
            r'sv1=([^&]*)',
            r'awc=([^&]*)',
            r'87121(?:_\d+|%5F\d+)?',
            r'awin\d\.com',
            r'awinmid=\d+',
            r'awinaffid=\d+'
        ]
        for pattern in url_patterns:
            matches = re.findall(pattern, text_lower)
            for match in matches:
                if isinstance(match, str):
                    for kw in self.keywords:
                        if kw.lower() in match.lower():
                            exact_matches.append(kw)
                        elif '87121' in match.lower() or 'gowithguide' in match.lower():
                            exact_matches.append(kw)
        return list(set(exact_matches))

    def extract_urls_from_onclick(self, element, source_url):
        if element.has_attr('onclick'):
            onclick = element['onclick']
            url_matches = re.findall(r'(?:window\.open|location\.href|window\.location)\s*=\s*[\'"](.+?)[\'"]', onclick)
            for url_match in url_matches:
                if url_match.startswith('http') or url_match.startswith('/'):
                    yield urljoin(source_url, url_match)
def generate_csv(results):
    csv_file = StringIO()
    writer = csv.DictWriter(csv_file, fieldnames=[
        'source_url', 'matched_url', 'keyword', 
        'location_type', 'element', 'attribute',
        'content_sample', 'timestamp'
    ])
    writer.writeheader()
    for result in results:
        writer.writerow({
            'source_url': result['source_url'],
            'matched_url': result['matched_url'],
            'keyword': result['keyword'],
            'location_type': result['location_type'],
            'element': result['element'],
            'attribute': result['attribute'],
            'content_sample': result['content'][:300] if result['content'] else '',
            'timestamp': result['timestamp']
        })
    return csv_file.getvalue()

def main():
    st.set_page_config(page_title="Enhanced Web Crawler", page_icon="🌐", layout="wide")
    
    st.markdown("""
        <script>
            function keepAlive() {
                fetch(window.location.href, {
                    method: 'GET',
                    headers: {
                        'Content-Type': 'application/json',
                        'Cache-Control': 'no-cache'
                    },
                    keepalive: true
                });
            }
            setInterval(keepAlive, 30000);
            let activityInterval = setInterval(() => {
                document.dispatchEvent(new Event('mousemove'));
            }, 60000);
            window.addEventListener('beforeunload', () => {
                clearInterval(activityInterval);
            });
        </script>
    """, unsafe_allow_html=True)

    st.markdown("""
        <style>
        @import url('https://fonts.googleapis.com/css2?family=Roboto:wght@400;500;700&family=Open+Sans:wght@400;600&display=swap');

        :root {
            --primary-color: #1976D2;
            --primary-light: #42A5F5;
            --primary-dark: #1565C0;
            --secondary-color: #26A69A;
            --background-light: #F5F5F5;
            --background-dark: #212121;
            --text-color-light: #212121;
            --text-color-dark: #FFFFFF;
            --card-color: rgba(255, 255, 255, 0.95);
            --card-color-dark: rgba(33, 33, 33, 0.95);
            --error-color: #D32F2F;
            --success-color: #388E3C;
            --warning-color: #FBC02D;
            --info-color: #0288D1;
        }

        body {
            font-family: 'Open Sans', sans-serif;
            margin: 0;
            padding: 0;
            background-color: var(--background-light);
            color: var(--text-color-light);
        }

        @media (prefers-color-scheme: dark) {
            body {
                background-color: var(--background-dark);
                color: var(--text-color-dark);
            }
            .card {
                background-color: var(--card-color-dark);
            }
        }

        .main-header {
            font-family: 'Roboto', sans-serif;
            font-size: 2.5rem;
            font-weight: 700;
            color: var(--primary-color);
            margin-bottom: 1.5rem;
            padding-bottom: 0.75rem;
            border-bottom: 3px solid var(--primary-light);
        }

        .description-text {
            font-size: 1.2rem;
            font-weight: 500;
            color: var(--text-color-light);
            margin-bottom: 1.5rem;
        }

        .subheader {
            font-family: 'Roboto', sans-serif;
            font-size: 1.8rem;
            font-weight: 600;
            color: var(--primary-dark);
            margin-top: 2rem;
            margin-bottom: 1rem;
        }

        .stButton>button {
            background-color: var(--primary-color);
            color: white;
            font-family: 'Open Sans', sans-serif;
            font-size: 1.1rem;
            font-weight: 600;
            border-radius: 8px;
            border: none;
            padding: 0.75rem 1.5rem;
            transition: background-color 0.3s;
            box-shadow: 0 3px 6px rgba(0, 0, 0, 0.16);
        }

        .stButton>button:hover {
            background-color: var(--primary-dark);
        }

        .stTextInput>div>input {
            background-color: var(--card-color);
            border: 1px solid var(--primary-light);
            border-radius: 8px;
            padding: 0.75rem;
            font-family: 'Open Sans', sans-serif;
            font-size: 1.1rem;
            color: var(--text-color-light);
            box-shadow: 0 2px 5px rgba(0, 0, 0, 0.12);
        }

        .stSelectbox>div>div>div {
            background-color: var(--card-color);
            border: 1px solid var(--primary-light);
            color: var(--text-color-light);
            font-family: 'Open Sans', sans-serif;
            font-size: 1.1rem;
        }

        .status-box {
            background-color: var(--card-color);
            color: var(--text-color-light);
            padding: 1.5rem;
            border-radius: 8px;
            border-left: 5px solid var(--primary-color);
            margin-bottom: 1.5rem;
            box-shadow: 0 3px 8px rgba(0, 0, 0, 0.12);
        }

        .results-box {
            background-color: var(--card-color);
            padding: 2rem;
            border-radius: 8px;
            margin-bottom: 2rem;
            box-shadow: 0 3px 10px rgba(0, 0, 0, 0.12);
        }

        .match-item {
            padding: 1.5rem;
            margin-bottom: 1.5rem;
            border-radius: 8px;
            border-left: 5px solid var(--secondary-color);
            background-color: var(--card-color);
            box-shadow: 0 2px 6px rgba(0, 0, 0, 0.12);
        }

        .url-display {
            font-family: monospace;
            background-color: #E0E0E0;
            padding: 0.75rem;
            border-radius: 4px;
            overflow-x: auto;
            font-size: 1rem;
            color: var(--text-color-light);
        }

        .keyword-tag {
            background-color: var(--primary-color);
            color: white;
            padding: 0.5rem 1rem;
            border-radius: 20px;
            font-size: 0.9rem;
            font-weight: 600;
            margin-right: 0.75rem;
        }

        .location-tag {
            background-color: var(--secondary-color);
            color: white;
            padding: 0.5rem 1rem;
            border-radius: 20px;
            font-size: 0.9rem;
            font-weight: 600;
        }

        .content-preview {
            background-color: #FAFAFA;
            border: 1px solid #E0E0E0;
            padding: 1rem;
            border-radius: 4px;
            font-family: monospace;
            font-size: 1rem;
            margin-top: 0.75rem;
            white-space: pre-wrap;
            overflow-x: auto;
            color: var(--text-color-light);
        }

        .progress-container {
            margin: 1.5rem 0;
        }

        .stProgress > div > div > div {
            background-color: var(--primary-color);
            border-radius: 4px;
        }

        @media (max-width: 768px) {
            .main-header { font-size: 2rem; }
            .subheader { font-size: 1.5rem; }
            .description-text, .stTextInput label, .stSelectbox label, 
            .status-box p, .results-box p, .results-box div, 
            .match-item strong, .match-item div { font-size: 1rem; }
            .stButton>button { font-size: 1rem; padding: 0.5rem 1rem; }
            .stTextInput>div>input, .stSelectbox>div>div>div { font-size: 1rem; }
        }
        </style>
    """, unsafe_allow_html=True)

    st.markdown('<h1 class="main-header">Enhanced Web Crawler</h1>', unsafe_allow_html=True)
    st.markdown('<p class="description-text">Search for GoWithGuide and affiliate references with advanced detection.</p>', unsafe_allow_html=True)
    
    st.markdown('<div class="card">', unsafe_allow_html=True)
    col1, col2 = st.columns([3, 1])
    with col1:
        url_input = st.text_input("Enter website URL:", "https://example.com", 
                                 help="Enter the full URL, including http:// or https://")
    with col2:
        crawl_mode = st.selectbox("Crawl Mode:", ["Quick", "Standard", "Complete"], index=1,
                                 help="Quick: Limited, Standard: Moderate, Complete: Thorough")
    col1, col2 = st.columns(2)
    with col1:
        start_btn = st.button("🔍 Start Crawling", help="Begin crawling")
    with col2:
        stop_btn = st.button("⛔ Stop & Reset", help="Stop and reset")
    st.markdown('</div>', unsafe_allow_html=True)

    if 'crawler' not in st.session_state:
        st.session_state.crawler = None
        st.session_state.running = False
        st.session_state.results = []
        st.session_state.status = []
        st.session_state.categories = []
    status_container = st.empty()
    progress_container = st.empty()
    results_container = st.empty()

    if start_btn and not st.session_state.running:
        if not url_input.startswith(('http://', 'https://')):
            url_input = f'https://{url_input}'
        st.session_state.crawler = EnhancedWebCrawler(start_url=url_input, crawl_mode=crawl_mode)
        st.session_state.running = True
        st.session_state.results = []
        st.session_state.status = [f"Starting crawl of {url_input} in {crawl_mode} mode"]
        st.session_state.categories = []

    if stop_btn:
        st.session_state.running = False
        if st.session_state.crawler:
            st.session_state.status.append("Crawl stopped by user")
        st.session_state.crawler = None
        st.session_state.results = []
        st.session_state.status = []
        st.session_state.categories = []

    if st.session_state.running and st.session_state.crawler:
        crawler = st.session_state.crawler
        with progress_container.container():
            st.markdown('<div class="progress-container">', unsafe_allow_html=True)
            progress_bar = st.progress(0)
            st.markdown('</div>', unsafe_allow_html=True)
        total_pages = crawler.max_pages

        if crawler.crawl_mode == "Quick":
            urls_to_crawl = [crawler.start_url]
            for i, url in enumerate(urls_to_crawl):
                if not st.session_state.running:
                    break
                st.session_state.status.append(f"Crawling: {url}")
                crawler.process_url(url)
                st.session_state.results = crawler.results
                progress_bar.progress((i + 1) / len(urls_to_crawl))
            st.session_state.running = False

        elif crawler.crawl_mode == "Standard":
            if not st.session_state.categories:
                homepage_links = crawler.get_main_pages()
                st.session_state.status.append(f"Crawling homepage and {len(homepage_links)} main pages...")
                urls_to_crawl = [crawler.start_url] + homepage_links
                for i, url in enumerate(urls_to_crawl[:crawler.max_pages]):
                    if not st.session_state.running:
                        break
                    st.session_state.status.append(f"Crawling: {url}")
                    crawler.process_url(url)
                    st.session_state.results = crawler.results
                    progress_bar.progress((i + 1) / min(crawler.max_pages, len(urls_to_crawl)))
                    if crawler.results:
                        st.session_state.status.append(f"Found {len(crawler.results)} matches")
                        break
                if not crawler.results:
                    st.session_state.categories = crawler.extract_categories()
                    if st.session_state.categories:
                        st.session_state.status.append(f"Found categories: {', '.join([c[0] for c in st.session_state.categories])}")
                    else:
                        st.session_state.status.append("No categories found.")
                        st.session_state.running = False
            elif st.session_state.categories:
                cat_name, cat_url = st.session_state.categories.pop(0)
                st.session_state.status.append(f"Processing category: {cat_name}")
                category_links = crawler.get_category_pages(cat_url)
                for i, url in enumerate(category_links[:crawler.max_pages]):
                    if not st.session_state.running:
                        break
                    st.session_state.status.append(f"Crawling: {url}")
                    crawler.process_url(url)
                    st.session_state.results = crawler.results
                    progress_bar.progress((i + 1) / min(crawler.max_pages, len(category_links)))
                    if crawler.results:
                        st.session_state.status.append(f"Found {len(crawler.results)} matches")
                        break
                if not st.session_state.categories and not crawler.results:
                    st.session_state.running = False

        elif crawler.crawl_mode == "Complete":
            while crawler.queue and crawler.pages_crawled < crawler.max_pages and st.session_state.running:
                url = crawler.queue.popleft()
                if url not in crawler.visited:
                    st.session_state.status.append(f"Crawling: {url} (Page {crawler.pages_crawled + 1}/{crawler.max_pages})")
                    new_urls = crawler.process_url(url)
                    for new_url in new_urls:
                        if (new_url not in crawler.visited and 
                            new_url not in crawler.queue and 
                            crawler.pages_crawled < crawler.max_pages):
                            crawler.queue.append(new_url)
                    st.session_state.results = crawler.results
                    progress_bar.progress(min(crawler.pages_crawled / crawler.max_pages, 1.0))
                    if crawler.results:
                        st.session_state.status.append(f"Found {len(crawler.results)} matches")
            if crawler.pages_crawled >= crawler.max_pages or not crawler.queue:
                st.session_state.running = False

        with status_container.container():
            st.markdown('<div class="status-box">', unsafe_allow_html=True)
            st.markdown('<h2 class="subheader">Status</h2>', unsafe_allow_html=True)
            for msg in st.session_state.status[-10:]:
                st.write(msg)
            st.markdown('</div>', unsafe_allow_html=True)

        if st.session_state.results:
            with results_container.container():
                st.markdown('<div class="results-box">', unsafe_allow_html=True)
                st.markdown(f'<h2 class="subheader">Matches Found ({len(st.session_state.results)})</h2>', unsafe_allow_html=True)
                for i, result in enumerate(st.session_state.results[-5:], 1):
                    st.markdown(f'<div class="match-item">', unsafe_allow_html=True)
                    st.markdown(f"**Match {i}:**", unsafe_allow_html=True)
                    st.markdown(f"<div><strong>Source URL:</strong> <span class='url-display'>{html.escape(result['source_url'])}</span></div>", unsafe_allow_html=True)
                    st.markdown(f"<div><strong>Matched URL:</strong> <span class='url-display'>{html.escape(result['matched_url'])}</span></div>", unsafe_allow_html=True)
                    st.markdown(f"<div><span class='keyword-tag'>{html.escape(result['keyword'])}</span> <span class='location-tag'>{html.escape(result['location_type'])}</span></div>", unsafe_allow_html=True)
                    st.markdown(f"<div><strong>Element:</strong> {html.escape(result['element'])} [{html.escape(result['attribute'])}]</div>", unsafe_allow_html=True)
                    if result['content']:
                        content_preview = result['content'][:100] + ('...' if len(result['content']) > 100 else '')
                        st.markdown(f"<div><strong>Content:</strong> <div class='content-preview'>{html.escape(content_preview)}</div></div>", unsafe_allow_html=True)
                    st.markdown('</div>', unsafe_allow_html=True)
                col1, col2, col3 = st.columns(3)
                with col1:
                    if st.button("💾 Save Results & Stop", key="save_results"):
                        csv_data = generate_csv(crawler.results)
                        st.download_button(
                            label="📥 Download CSV",
                            data=csv_data,
                            file_name=f"crawl_report_{datetime.datetime.now().strftime('%Y%m%d_%H%M%S')}.csv",
                            mime="text/csv"
                        )
                        st.session_state.running = False
                        crawler.user_stopped = True
                with col2:
                    if st.button("🔄 Continue to Next Category", key="next_category") and crawler.crawl_mode != "Complete":
                        crawler.pages_crawled = 0
                with col3:
                    if st.button("⏩ Continue Current Category", key="current_category") and crawler.crawl_mode != "Complete":
                        crawler.pages_crawled = 0
                st.markdown('</div>', unsafe_allow_html=True)

        if not st.session_state.running and st.session_state.results and not crawler.user_stopped:
            csv_data = generate_csv(crawler.results)
            st.download_button(
                label="📥 Download Final Results",
                data=csv_data,
                file_name=f"crawl_report_{datetime.datetime.now().strftime('%Y%m%d_%H%M%S')}.csv",
                mime="text/csv"
            )

if __name__ == "__main__":
    main()
