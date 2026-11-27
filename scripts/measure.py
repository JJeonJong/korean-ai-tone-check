#!/usr/bin/env python3
"""ai-tone-check 측정기 v2.2.1.

긴 한국어 글에서 AI가 쓴 글에 많은 표면 특징을 재서 '다시 볼 곳'을 알려 준다. 판정기가 아니다.

기준값(TH)
  general : 2022년 11월 이전에 사람이 쓴 한국어 기술 글의 절반으로 잡고 나머지 절반으로 확인했다.
            항목마다 그 글의 95% 이상이 통과하는 선이다(끝맺음과 '~적'은 그보다 느슨하게 잡았다).
            위키백과, 경제 기사, KatFish(Park 외, ACL 2025)의 학생 논증문과 2024년 LLM 논증문,
            지금 모델이 쓴 초안 21편에서도 표시율을 쟀다.
  academic: KatFish의 연구자 초록·논문 본문과 LLM 초록으로 잡았다.
수치와 한계는 SKILL.md의 '기준값과 한계' 절에 있다.

사용법
  python measure.py 글.md                    측정 (일반 글 기준)
  python measure.py 글.md --genre academic   논문·초록 기준으로 측정
  python measure.py 글.md --mark             측정하고, 지금 내용을 비교 기준본으로 저장
  python measure.py 글.md --compare          측정하고, 기준본과 비교 (변경률, 바뀐 곳, 바뀐 숫자·영문 표기)
  python measure.py 글.md --mark --reset     기준본을 지금 내용으로 새로 잡는다
  python measure.py 글.md --forget           이 글의 기준본을 지운다(--scratch로 받은 임시 초안이면 초안 파일도)
  python measure.py --diff 전.md 후.md       두 파일만 비교
  python measure.py --scratch                채팅용 글을 저장할 임시 파일 경로를 알려 준다

기준본과 임시 초안은 시스템 임시 폴더 아래 사용자 전용 폴더(ai-tone-check-<사용자 번호>, 윈도우는 ai-tone-check)에
두고, 이 도구가 만든 파일은 14일이 지나면 지운다.
"""

import argparse
import bisect
import difflib
import errno
import hashlib
import math
import os
import re
import stat
import statistics
import sys
import tempfile
import time
import unicodedata
from collections import Counter

VERSION = "2.2.1"
MIN_SENT = 8      # 비율 지표를 계산할 최소 한국어 문장 수
MIN_STYLE = 20    # 문장 길이·끝맺음 지표를 계산할 최소 한국어 문장 수(짧은 글에서는 값이 크게 흔들린다)
MAX_EX = 3        # 항목당 보여 줄 예시 수
WINDOW = 8        # 끝맺음 다양성을 보는 문장 창 크기
LABEL_MAX = 60    # 마침표 없이 끝난 이 길이 이하의 한 줄 문단은 제목처럼 본다(서술어로 끝난 문장은 빼고)
KEEP_HOURS = 12   # 이 시간 안에 잡은 기준본은 --mark로 덮어쓰지 않는다
KEEP_DAYS = 14    # 기준본과 임시 초안을 두는 기간
WORK_MAX = 12000000   # 비교: 어절을 맞대는 일의 한도. 넘으면 어순을 무시하고 어림한다(실제 글은 길어도 300만을 넘지 않았다)
GAP_MAX = 40      # 비교: 바뀐 두 곳 사이가 이보다 멀면 문장 끝 표시가 없어도 다른 곳으로 본다
CONTEXT_MAX = 20  # 비교: 바뀐 곳을 문장으로 넓힐 때 한쪽에 더하는 어절 수의 한도
LONG_RUN = 120    # 비교: 통째로 바뀐 구간이 이보다 길면 가운데를 줄여 보여 준다
SHOW_MAX = 15     # 비교: 보여 줄 바뀐 곳 수

# 기준값: (기준, 최소 횟수). None이면 그 장르에서는 사람 글과 차이가 확인되지 않아 값만 보여 준다.
# 비율은 0~1, 밀도는 1,000자당 횟수, 횟수는 '이상'이면 표시.
TH = {
    "general": {
        "comma_ratio": (0.50, 0),    # 쉼표가 든 문장 비율 (초과)
        "conn_comma": (6.5, 3),      # 연결어미·접속어 뒤 쉼표 밀도 (초과)
        "len_cv": (0.35, 0),         # 문장 길이 변동계수 (미만)
        "end_top": (0.65, 0),        # 가장 많이 쓴 끝맺음의 비율 (초과)
        "opener_ratio": (0.20, 0),   # 격식 접속어로 시작하는 문장 비율 (초과)
        "pivot": (1, 0),             # 문두 '결론적으로' 횟수 (이상)
        "deictic": (1.5, 2),         # '이는/이러한/이를 통해'로 시작하는 문장 밀도 (초과)
        "dayanghan": (1.5, 2),       # '다양한' 밀도 (초과)
        "preachy": (0.5, 1),         # '~는 것이 중요하다', '노력해야' 밀도 (초과)
        "simply_not": (0.5, 1),      # '단순히 ~가 아니라' 밀도 (초과)
        "jeok": (5.0, 3),            # '~적인/~적으로' 밀도 (초과)
    },
    "academic": {
        "comma_ratio": (0.60, 0),
        "conn_comma": (6.0, 3),
        "len_cv": None,
        "end_top": None,
        "opener_ratio": None,
        "pivot": (1, 0),
        "deictic": None,
        "dayanghan": None,
        "preachy": (0.5, 2),
        "simply_not": (0.5, 2),
        "jeok": None,
    },
}
TH_COMMON = {"chatbot": (1, 0), "em_dash": (3, 0)}   # 장르와 무관한 기준
# '참고'로만 보여 주는 밀도 항목: (기준, 최소 횟수)
NOTE_TH = {
    "general": {"can": (7.0, 3), "through": (3.0, 3), "bold": (1.0, 3)},
    "academic": {"bold": (1.0, 3)},
}
GENRE_NAME = {"general": "일반 글", "academic": "논문·초록"}

# '확인 필요' 후보: (키, 이름, 방식, 종류).  방식은 over(초과) | under(미만) | count(횟수 이상).
# 종류가 같은 항목은 한 가지 습관을 두 번 잰 것이라 묶어서 센다.
STRONG = (
    ("comma_ratio", "쉼표가 든 문장", "over", "쉼표"),
    ("conn_comma", "연결어미·접속어 뒤 쉼표", "over", "쉼표"),
    ("len_cv", "문장 길이 변동계수", "under", "문장 길이"),
    ("end_top", "한 가지 끝맺음에 몰린 문장", "over", "끝맺음"),
    ("opener_ratio", "격식 접속어로 시작하는 문장", "over", "문두 표지"),
    ("pivot", "문두 '결론적으로'", "count", "문두 표지"),
    ("deictic", "'이는/이러한/이를 통해'로 시작하는 문장", "over", "문두 지시어"),
    ("dayanghan", "'다양한'", "over", "'다양한'"),
    ("preachy", "'~는 것이 중요하다', '노력해야' 류", "over", "당부 표현"),
    ("simply_not", "'단순히 ~가 아니라'", "over", "부정 병렬"),
    ("jeok", "'~적인/~적으로'", "over", "'~적'"),
    ("chatbot", "챗봇 말투", "count", "챗봇 말투"),
    ("em_dash", "em dash(—)", "count", "em dash"),
)
# '참고': (키, 이름, 보여 줄 최소 횟수, 글 길이에 따라 늘릴지)
NOTES = (
    ("closing", "마지막 세 문장의 당부·전망 표현", 1, False),
    ("pivot_other", "문두 정리 표지(요약하면, 정리하면, 요컨대)", 1, False),
    ("greeting", "맺음 인사(도움이 되었으면, 궁금한 점이 있으시면). 메일·블로그에서는 자연스럽다", 1, False),
    ("ordinal", "문두 서수 나열(첫째, 둘째)", 2, False),
    ("pronoun", "'그것은/그들은' 류 대명사", 2, True),
    ("soft", "'~것으로 보인다', '가능성이 있다' 류", 2, True),
    ("formal_noun", "'~것이다/~것입니다'", 3, True),
    ("calque", "번역투(되어지다, ~에 있어서는)", 1, True),
    ("cliche", "상투어·과장어", 1, True),
    ("preview", "예고 멘트(살펴보겠습니다)", 1, True),
    ("authority", "출처 없는 권위(전문가들은)", 1, True),
    ("emoji", "이모지", 1, False),
    ("inline_header", "굵은 머리말 목록(- **항목:**). 서식 취향 항목", 3, False),
    ("colon_heading", "콜론 부제 제목(X: Y)", 2, False),
    ("title_case", "영어 Title Case 제목", 2, False),
    ("paren_en", "괄호 영어 병기 반복", 1, False),
    ("en_vocab", "영어 AI 단골 어휘", 2, False),
    ("en_pattern", "영어 상투 구조", 2, False),
)
NOTE_LABEL = {
    "can": "'~ㄹ 수 있' (능력·기능을 뜻하면 그대로 둔다)",
    "through": "'~을 통해' (사람이 쓴 글에도 흔하다. 거듭 나올 때만 본다)",
    "bold": "볼드 (서식 취향 항목. 사람이 쓴 기술 글에도 흔하다)",
}
RATIO_KEYS = {"comma_ratio", "opener_ratio", "end_top"}
DENSITY_KEYS = {"conn_comma", "deictic", "dayanghan", "preachy", "simply_not", "through", "jeok", "can", "bold"}

# 임시 폴더에서 이 도구가 만든 파일: 기준본, 임시 초안, 쓰다 만 임시 파일
OWN_FILE = re.compile(r"^(?:[0-9a-f]{16}\.txt|draft-\d{8}-\d{6}-\d{3}\.md|\.tmp-[A-Za-z0-9_]+)$")
DRAFT_FILE = re.compile(r"^draft-\d{8}-\d{6}-\d{3}\.md$")
HANGUL = re.compile(r"[가-힣]")
LATIN = re.compile(r"[A-Za-z]")
DOT = "\u2024"   # 문장을 나눌 때 약어·날짜·번호의 마침표를 잠시 바꿔 두는 문자
ELL = "\u22ef"   # 문장 가운데 말줄임표를 잠시 바꿔 두는 문자
PUA0, PUA_MAX = 0xE000, 6000   # 줄 번호를 실어 나르는 사설 영역 문자
PUA_RE = re.compile("[\ue000-\uf8ff]")

# -- 마크다운 구조 ---------------------------------------------
FENCE = re.compile(r"^ {0,3}(`{3,}|~{3,})(.*)$")
SETEXT_EQ = re.compile(r"^ {0,3}=+\s*$")
SETEXT_DASH = re.compile(r"^ {0,3}-+\s*$")
HRULE = re.compile(r"^ {0,3}([-*_])(?:\s*\1){2,}\s*$")
LIST_ITEM = re.compile(r"^\s*(?:[-*+]|\d{1,3}[.)])\s+(?:\[[ xX]\]\s+)?")
TABLE_SEP = re.compile(r"^\|?\s*:?-{2,}:?\s*(?:\|\s*:?-{2,}:?\s*)*\|?$")
QUOTE = re.compile(r"^ {0,3}>")
FRONT_KEY = re.compile(r"^[A-Za-z_가-힣][\w가-힣 \-]*:")
TOML_KEY = re.compile(r"^[A-Za-z_][\w\-]*\s*=")
REF_DEF = re.compile(r"^ {0,3}\[[^\]]+\]:\s")
INDENTED = re.compile(r"^(?: {4,}|\t)")
RAW_OPEN = re.compile(r"^ {0,3}<(pre|script|style)\b", re.I)   # 줄 맨 앞의 여는 태그만(본문에서 언급한 태그 이름은 아니다)
# 캡션: 번호 뒤에 구분 기호가 있어야 한다('그림 2. 실험 절차'). '그림 2 참조 후 보냈다.'는 문장이다
CAPTION = re.compile(r"^(?:그림|표|사진|도표|코드|수식|Figure|Fig\.?|Table|Listing)\s*\d+(?:[.\-]\d+)*\s*[.:：]\s")
PREDICATE_END = re.compile(r"[가-힣](?:다|요|죠|까)$")   # 서술어로 끝난 줄
FOOTNOTE_DEF = re.compile(r"^ {0,3}\[\^[^\]]+\]:")
ZERO_WIDTH = re.compile("[\u200b\u2060\ufeff\u00ad]")   # 폭 없는 공백, 문서 중간의 BOM, 소프트 하이픈
VERBAL_COLON = re.compile(r"[다요죠까]\s*[:：]\s*$")

# -- 인라인 요소 -----------------------------------------------
HTML_CODE = re.compile(r"<(pre|code|script|style|kbd|samp)\b[^>]*>.*?</\1\s*>", re.I | re.S)
INLINE_MATH = re.compile(r"(?<![\\$A-Za-z0-9])\$(?![\s$])[^$\n]{1,200}?(?<![\s\\])\$(?![A-Za-z0-9$])|\\\([^\n]{1,200}?\\\)")
URL = re.compile(r"https?://[^\s<>]+")
URL_TAIL = ".,;:!?)]}'\"」』"   # 주소 끝에 붙은 문장부호는 주소가 아니다
TAG = re.compile(r"</?[A-Za-z][A-Za-z0-9-]*(?:\s+[A-Za-z_:@][\w:.@-]*(?:\s*=\s*(?:\"[^\"]*\"|'[^']*'|[^\s\"'<>=]+))?)*\s*/?>")
# 짧은 인용·언급(40자 이하). 곧은 따옴표는 여닫는 모양이 같아서, 여는 쪽 바로 뒤와 닫는 쪽 바로 앞에
# 공백이 없을 때만 짝으로 본다('90년대 … '핵심'에서 앞의 둘을 짝짓지 않게).
QUOTED = re.compile(r"[‘“「『][^‘’“”「」『』\n]{1,40}[’”」』]"
                    r"|(?<![A-Za-z가-힣0-9])'(?!\s)[^'\n]{1,40}(?<!\s)'(?![A-Za-z0-9])"
                    r"|(?<![A-Za-z가-힣0-9])\"(?!\s)[^\"\n]{1,40}(?<!\s)\"(?![A-Za-z0-9])")

# -- 문장 나누기 -----------------------------------------------
ABBR = re.compile(r"\b(?:et al|etc|Figs?|Eqs?|Sec|Tab|Refs?|Vol|pp|vs|cf|Dr|Prof|Mr|Mrs|Ms|Inc|Ltd|e\.g|i\.e|approx|Ph\.D|U\.S)\."
                  r"(?=[\s,)\]])|\b(?:No|p|Ch|Art)\.(?=\s?\d)", re.I)
DATE = re.compile(r"(?<!\d)\d{4}\.\s?\d{1,2}\.(?:\s?\d{1,2}\.)?")
ENUM = re.compile(r"(?:(?<=\s)|^)([1-9])\.(?=\s+[가-힣A-Za-z])")
ELLIPSIS_MID = re.compile(r"(?<=[가-힣])(?<![다요까죠네])(?:\.{2,}|…+)(?=\s+[가-힣A-Za-z])")
TERMINATORS = ".!?…"
CLOSERS = "\"'”’)]」』"
ENDED = re.compile(r"[.!?…][\"'”’)\]」』]*$")
TRAIL_CHARS = frozenset(".!?…,;:~\"'”’)]」』>*")   # 끝맺음을 읽을 때 문장 끝에서 떼어 내는 문자(공백도 뗀다)
TAIL_CHARS = frozenset(".!?…\"'”’」』")           # 문장 끝의 문장부호(공백도 포함)
PAIRS = (("(", ")"), ("“", "”"), ("‘", "’"), ("「", "」"), ("『", "』"))

# -- 쉼표 -----------------------------------------------------
THOUSANDS = re.compile(r"(?<![\d,])\d{1,3}(?:,\d{3})+(?![\d,])")
ANY_COMMA = re.compile(r"[,，]")
WORD_COMMA = re.compile(r"([가-힣]{1,30})[,，]")
PHRASE_COMMA = re.compile(r"(?:예를 들어|이를 통해|이를 위해|이에 따라|이와 같이|이로 인해|그 결과|이 때문에|뿐만 아니라|그럼에도 불구하고)[,，]")
CONN_TAILS = ("더라도", "음에도", "는데도", "지만", "면서", "는데", "은데", "인데", "어서", "아서", "여서", "해서", "니까", "므로",
              "거나", "도록", "려고", "하면", "되면", "으면", "다면", "려면", "보면", "자면", "아니라", "하여", "되어", "으나",
              "고", "며")
CONN_WORDS = {"통해", "위해", "인해"}
CONN_ADV = {"그러나", "하지만", "그래서", "그런데", "그리고", "또한", "따라서", "그러므로", "즉", "특히", "한편", "아울러", "더불어",
            "나아가", "결국", "물론", "다만", "먼저", "우선", "이처럼", "반면", "반면에", "결과적으로", "결론적으로",
            "요약하면", "정리하면", "종합하면", "마지막으로", "다음으로", "게다가", "더욱이", "예컨대", "가령",
            "첫째", "둘째", "셋째", "넷째", "그럼에도", "그렇지만", "이어서", "왜냐하면", "요컨대"}
# '고'로 끝나지만 연결어미가 아닌 명사. 이 말로 끝나는 합성어('물류창고')도 뺀다.
GO_NOUNS = ("최고", "광고", "경고", "원고", "창고", "금고", "로고", "망고", "권고", "예고", "공고", "중고", "선고", "수고",
            "국고", "문고", "숙고", "퇴고", "제고", "냉장고", "무기고", "격납고", "변고", "부고", "출고", "태고", "상고",
            "항고", "포고", "탈고", "투고", "장고", "회고", "해고", "통고", "유고", "무고", "외고", "과학고", "특목고",
            "자사고", "일반고", "생활고", "초고", "잔고", "연고", "여고", "노고", "레고", "시카고", "탄약고", "보관고",
            "특성화고", "마이스터고", "업무보고", "결과보고", "현장보고", "허위보고", "중간보고", "최종보고")
# 명사와 동사 활용형이 같은 말('보고서 보고' / '책을 보고'): 앞 어절이 '을/를/이/가'로 끝날 때만 연결어미로 센다
GO_AMBIG = {"보고", "사고", "기고", "입고", "재고", "신고", "피고", "차고", "서고", "참고", "비고", "남고"}
GO_COMPOUND = ("사고", "신고", "재고")   # 이 말로 끝나는 세 글자 이상은 합성 명사('교통사고')로 본다
PARTICLE_BEFORE = re.compile(r"[을를이가]\s*$")

# -- 문두 표지 -------------------------------------------------
OPENERS = ("또한", "따라서", "그러므로", "그러나", "특히", "결론적으로", "결과적으로", "요약하면", "요약하자면",
           "정리하면", "정리하자면", "종합하면", "종합적으로", "예를 들어", "마지막으로", "먼저", "우선", "나아가",
           "아울러", "더불어", "한편", "즉", "무엇보다", "반면", "반면에", "이에 따라", "이와 같이", "뿐만 아니라",
           "게다가", "더욱이", "다음으로")
DEICTIC = ("이는", "이러한", "이를 통해", "이로 인해", "이를 위해", "이와 같은")
PIVOTS = ("결론적으로",)
PIVOTS_OTHER = ("요약하면", "요약하자면", "정리하면", "정리하자면", "종합하면", "종합해 보면", "종합적으로", "요컨대", "한마디로")
LEAD = r"^[\"'“‘(]?\s*"


def _initial(words):
    alt = "|".join(map(re.escape, sorted(words, key=len, reverse=True)))
    return re.compile(LEAD + r"(?:" + alt + r")(?=[\s,，]|$)")


OPENER_RE, DEICTIC_RE, PIVOT_RE, PIVOT_OTHER_RE = (_initial(w) for w in (OPENERS, DEICTIC, PIVOTS, PIVOTS_OTHER))
# '첫째는'은 맏이를 뜻할 수 있어 쉼표나 '로'가 붙은 꼴만 센다
ORDINAL_RE = re.compile(LEAD + r"(?:(첫째|둘째|셋째|넷째)(?:[,，]|로[,，\s])"
                               r"|(첫 번째|두 번째|세 번째|네 번째)(?:[,，]|로[,，\s]|는[\s,，]|\s(?:이유|문제|방법|단계|특징|장점|원인|요인|원칙)[은는이가]))")


def rx(*patterns):
    return [re.compile(p) for p in patterns]


# -- 표현 목록 -------------------------------------------------
P_DAYANGHAN = rx(r"다양한(?!데)")
P_PREACHY = rx(r"는 (?:것이|게) (?:중요|필요|바람직)(?!한[\s,.]|한$|하지 ?않|하지는|치 ?않| ?없)",
               r"노력(?:해야|이 필요)", r"중요한 역할을")
P_SIMPLY = rx(r"단순(?:히|한) [^.!?\n]{0,40}?(?:아니라|아닌(?!지)|[을를] 넘어(?![가갔간갈])|넘어서)")
P_THROUGH = rx(r"[을를] 통(?:해|한|하여)")
JEOK = re.compile(r"([가-힣]{1,3}적)(?:인데|인지|인가|이지만|이라고|이라는|이라|으로(?:는|도|만|써|서)?|이다|입니다|이며|이고|인|일)(?![가-힣])")
# '-적(的)'이 아니라 '적'으로 끝나는 명사
# 이 말로 끝나면 언제나 명사다('주목적', '총누적')
JEOK_TAILS = ("목적", "흔적", "추적", "축적", "궤적", "누적", "필적", "숙적", "강적", "퇴적", "쾌적")
# 낱말 그대로일 때만 명사다. 앞에 한 글자가 붙으면 '-적' 말이 된다('체적'과 '구체적', '본적'과 '기본적')
JEOK_NOUNS = ("실적", "성적", "업적", "면적", "기적", "표적", "서적", "국적", "행적", "유적", "족적", "해적", "산적",
              "도적", "천적", "체적", "용적", "선적", "호적", "본적", "무적", "한적")
JEOK_COMPOUNDS = {"연면적", "총면적", "단면적", "고서적", "무국적"}   # 세 글자 명사
JEOK_PREFIX = "비초반중범탈무준불몰"   # 네 글자 이상에서 이 글자로 시작하면 '-적' 말('비현실적'), 아니면 합성 명사('연구실적')
JEOK_ADVERBS = ("결론적으로", "결과적으로", "종합적으로")   # 문두 표지로 따로 세는 말
P_CAN = rx(r"(?<=[가-힣] )수 있")
P_CHATBOT = rx(r"물론(?:입니다|이죠|이에요)", r"(?:좋은|훌륭한|흥미로운|날카로운) 질문(?:입니다|이에요|이네요|이군요|[!.])",
               r"(?:저는|제가|전) (?:[^.!?\n]{0,12} )?(?:AI|인공지능)(?: 언어 ?모델| 어시스턴트| 비서| 챗봇)?"
               r"(?:로서|이기|이라서|라서|입니다|이므로)",
               r"(?:AI|인공지능) 언어 ?모델(?:로서|이기 때문에?|이라서|이므로)[^.!?\n]{0,40}(?:저는|제가|드릴|드리|없습니다|어렵습니다|못합니다)",
               r"(?:AI|인공지능) 언어 ?모델인 저", r"기꺼이 도와",
               r"(?i)\bI hope this helps", r"(?i)\bgreat question", r"(?i)\bcertainly!", r"(?i)\blet me know if",
               r"(?i)\bas of my (?:last|knowledge)")
# 아래는 '참고'로만 보여 주는 표현
P_NOTE = {
    "greeting": rx(r"도움이 (?:되었|되셨|됐)(?:으면|길|기를)", r"도움이 되(?:길|기를)",
                   r"궁금한 (?:점|사항)이 (?:있으시|있다면|있으면)", r"언제든(?:지)? (?:물어|말씀|문의|연락)"),
    "pronoun": rx(r"(?<![가-힣])(?:그것은|그것이|그들은|그들이|그들의)(?![가-힣])"),
    "soft": rx(r"것으로 (?:보인다|보입니다|예상된다|예상됩니다|판단된다|판단됩니다)", r"가능성이 (?:있|높|크)", r"경향이 있"),
    "formal_noun": rx(r"(?<= )것(?:이다|입니다)"),
    "calque": rx(r"(?:되어|보여|쓰여|불려|놓여|잊혀)(?:지|진|졌|질|져)", r"함에 있어", r"에 있어서(?:는|도|의)", r"에 있어,"),
    "cliche": rx(r"시사하는 바가", r"주목할 만", r"눈여겨볼", r"본질적으로", r"다채로운", r"진정한 의미",
                 r"혁신적(?:인|으로)", r"획기적(?:인|으로)", r"자리매김", r"핵심적(?:인|으로)", r"이정표", r"한 획을",
                 r"새로운 지평", r"게임 체인저", r"무한한 가능성", r"시너지"),
    "preview": rx(r"(?:살펴|알아|짚어|정리해) ?(?:보겠|봅시다|보자|보도록)"),
    "authority": rx(r"전문가들(?:은|이|에 따르면)", r"알려진 바에 따르면", r"학계의 중론"),
}
# 문장 끝의 서술어만 본다('필요한 전압은 5V다' 같은 문장은 걸리지 않게)
END = r"[\s.!\"'”’)]*$"
CLOSING = {
    "general": re.compile(r"(?:중요|필요)(?:하다|합니다|할 것이다|할 것입니다)" + END + r"|노력(?:해야|이 필요)|(?:바란다|바랍니다)" + END
                          + r"|기여할 것|도움이 될 것|더 나은 (?:미래|내일|세상|사회)(?!라는|이라는)"),
    "academic": re.compile(r"기대(?:된다|됩니다)" + END + r"|기여할 (?:것|수)|가능성을 (?:보여|제시|확인)"
                           r"|(?:중요|필요)(?:하다|합니다)" + END),
}
EN_VOCAB = rx(r"(?i)\bdelv(?:e|es|ed|ing)\b", r"(?i)\bintricat(?:e|ely)\b", r"(?i)\bintricac(?:y|ies)\b",
              r"(?i)\bmeticulous(?:ly)?\b", r"(?i)\bcommendable\b", r"(?i)\bunderscor(?:e|es|ed|ing)\b",
              r"(?i)\bshowcas(?:e|es|ed|ing)\b", r"(?i)\bpivotal\b", r"(?i)\btapestry\b", r"(?i)\btestament\b",
              r"(?i)\bboast(?:s|ed|ing)?\b", r"(?i)\bcomprehend(?:s|ed|ing)?\b")
EN_PATTERN = rx(r"(?i)\bserves? as\b", r"(?i)\bstands? as\b", r"(?i)\bplays? an? \w+ role\b",
                r"(?i)\bit(?:'s| is) worth noting\b", r"(?i)\bin conclusion\b", r"(?i)\bin today'?s\b",
                r"(?i)\bever-evolving\b", r"(?i)\bthe future looks bright\b", r"(?i)\bnot (?:just|only|merely)\b")

# -- 서식 -----------------------------------------------------
BOLD = re.compile(r"\*\*[^*\n]+\*\*|(?<![\w가-힣])__[^_\n]+__(?![\w가-힣])")
INLINE_HEADER = re.compile(r"^(?:\*\*[^*]+(?:\*\*\s*[:：]|[:：]\s*\*\*)|__[^_]+(?:__\s*[:：]|[:：]\s*__))")
EM_DASH = re.compile(r"[—―]")
_EMO = "\U0001F000-\U0001FAFF\u2600-\u27BF\u2B50\u2B55"
_MOD = "\uFE0F\U0001F3FB-\U0001F3FF"
EMOJI = re.compile(f"[{_EMO}][{_MOD}]?(?:\u200D[{_EMO}][{_MOD}]?)*|[0-9#*]\uFE0F?\u20E3")   # 이어 붙인 이모지는 하나로 센다
PAREN_EN = re.compile(r"[가-힣]\s?\(([A-Za-z][A-Za-z0-9 .,&+#/\-]{1,})\)")
PAREN_CITE = re.compile(r"et al|,\s*(?:19|20)\d{2}")
SMALL_WORDS = {"a", "an", "the", "and", "or", "but", "of", "in", "on", "at", "to", "for", "with", "by", "vs"}

# -- 비교 -----------------------------------------------------
NUM_TOKEN = re.compile(r"(?:(?<![\w.,)\]%])[-+−±])?\d+(?:,\d{3})*(?:\.\d+)?%?")
LATIN_TOKEN = re.compile(r"[A-Za-z][A-Za-z0-9+#_\-]*[A-Za-z0-9+#]|(?<![A-Za-z0-9])[A-Za-z](?![A-Za-z0-9])")
NEW_BLOCK = re.compile(r"^\s*(?:[-*+]\s|\d{1,3}[.)]\s|#{1,6}\s|\||>)")   # 목록 항목, 제목, 표의 줄, 인용 줄이 시작되는 줄
ONE_LINE = re.compile(r"^\s*(?:#{1,6}\s|\|)")                              # 한 줄로 끝나는 것: 제목, 표의 줄
WORD_EDGE = ".,;:!?()[]{}\"'“”‘’「」『』…"


# ============================================================
# 읽기와 구조 분석
# ============================================================
def decode(data, name):
    encodings = ("utf-16",) if data[:2] in (b"\xff\xfe", b"\xfe\xff") else ("utf-8-sig", "cp949")
    for enc in encodings:
        try:
            return data.decode(enc)
        except UnicodeDecodeError:
            continue
    sys.exit(f"인코딩을 알 수 없습니다(UTF-8, CP949, UTF-16 아님): {name}")


def read_text(path):
    if path == "-":
        sys.exit("표준입력은 받지 않습니다. 글을 파일로 저장한 뒤 그 경로를 주세요.")
    try:
        with open(path, "rb") as f:
            return decode(f.read(), path)
    except OSError as e:
        sys.exit(f"파일을 열 수 없습니다: {path} ({e.strerror})")


def rtrim(s, chars):
    """끝에 붙은 공백과 chars의 문자를 떼어 낸다. 정규식 '[…]+$'는 그런 문자가 수천 개 이어진 글에서 아주 느려서 직접 센다."""
    i = len(s)
    while i and (s[i - 1] in chars or s[i - 1].isspace()):
        i -= 1
    return s[:i]


def cut_url(m):
    """주소를 공백으로 바꾸되 끝에 붙은 문장부호는 남긴다('…/docs.' 의 마침표)."""
    rest = m.group(0)[m.group(0).index("//") + 2:]
    core = rest.rstrip(URL_TAIL) or rest[:1]
    return " " + rest[len(core):]


def atx_heading(line):
    """'# 제목' 꼴이면 제목 글을, 아니면 None을 돌려준다. 뒤에 붙은 닫는 '#'은 뗀다('## 제목 ##')."""
    s = line.lstrip(" ")
    k = len(s) - len(s.lstrip("#"))
    if len(line) - len(s) > 3 or not 1 <= k <= 6 or len(s) == k or not s[k].isspace():
        return None
    body = s[k:].strip()
    bare = body.rstrip("#")
    if bare != body and bare and bare[-1].isspace():
        body = bare.rstrip()
    return body


def strip_inline(s):
    """주석, 인라인 코드, 수식, 링크 주소, 태그를 걷어 낸다. 강조 표시(**)는 남긴다."""
    k = s.rfind("-->")
    if k >= 0:   # 닫는 표시가 있는 데까지만 본다(닫히지 않은 '<!--'가 수천 개 이어져도 느려지지 않게)
        s = re.sub(r"<!--.*?-->", " ", s[:k + 3], flags=re.S) + s[k + 3:]
    s = HTML_CODE.sub(" ", s)
    s = re.sub(r"``.+?``|`[^`\n]*`", " ", s)
    s = INLINE_MATH.sub(" ", s)
    s = re.sub(r"!\[([^\]]{0,300})\]\([^)]{0,500}\)", r"\1", s)
    s = re.sub(r"\[\[[^\]|]{0,200}\|([^\]]{0,200})\]\]", r"\1", s)
    s = re.sub(r"\[\[([^\]]{0,200})\]\]", r"\1", s)
    s = re.sub(r"\[([^\]]{0,300})\]\([^)]{0,500}\)", r"\1", s)
    s = re.sub(r"\[([^\]]{1,300})\]\[[^\]]{0,100}\]", r"\1", s)
    s = re.sub(r"\[\^[^\]]{1,50}\]", "", s)
    s = URL.sub(cut_url, s)
    return TAG.sub(" ", s)


def plain(s):
    """강조 표시까지 걷어 낸 본문."""
    s = re.sub(r"\*\*([^*\n]+)\*\*", r"\1", s)
    s = re.sub(r"(?<![\w가-힣])__([^_\n]+)__(?![\w가-힣])", r"\1", s)
    s = re.sub(r"(?<![\w*])\*([^*\n]+)\*(?![\w*])", r"\1", s)
    s = re.sub(r"~~([^~\n]+)~~", r"\1", s)
    s = re.sub(r"\s+", " ", s).strip()
    return re.sub(r"(?<=[^\s.,!?…]) (?=[.,!?](?: |$))", "", s)   # 주소 등을 걷어 낸 자리의 '말 .'을 '말.'로


def unmark(s, line_nos):
    """줄 표지를 걷어 낸 글과 [(글자 위치, 원래 줄 번호)]를 돌려준다."""
    out, starts = [], []
    for ch in s:
        code = ord(ch)
        if PUA0 <= code <= PUA0 + PUA_MAX:
            starts.append((len(out), line_nos[min(code - PUA0, len(line_nos) - 1)]))
        elif ch.isspace():
            if out and out[-1] != " ":
                out.append(" ")
        else:
            out.append(ch)
    while out and out[-1] == " ":
        out.pop()
    if not starts or starts[0][0] > 0:
        starts.insert(0, (0, line_nos[0]))
    return "".join(out), starts


def line_of(starts, pos):
    return starts[max(bisect.bisect_right(starts, (pos, float("inf"))) - 1, 0)][1]


def hangul_share(s):
    chars = re.sub(r"\s", "", s)
    return len(HANGUL.findall(chars)) / len(chars) if chars else 0.0


def table_rows(lines):
    mark = [False] * len(lines)
    for i, line in enumerate(lines):
        s = line.strip()
        if "|" in s and TABLE_SEP.match(s) and i > 0 and "|" in lines[i - 1]:
            mark[i - 1] = mark[i] = True
            j = i + 1
            while j < len(lines) and lines[j].strip() and "|" in lines[j]:
                mark[j] = True
                j += 1
        elif len(s) > 1 and s.startswith("|") and s.endswith("|"):
            mark[i] = True
    return mark


def cut_comments(line, inside, closes_later):
    """줄에서 HTML 주석을 걷어 낸다. (남은 글, 줄 끝에서 주석이 열려 있는지, 이 줄에서 연 주석 수)

    줄 가운데서 열고 닫지 않은 '<!--'는 뒤쪽 줄에 '-->'가 있을 때만 주석으로 본다(글에서 기호를 언급한 경우).
    """
    out, i, opened = [], 0, 0
    ticks, seen = 0, 0   # line[:seen]에 든 백틱 수
    while True:
        if inside:
            j = line.find("-->", i)
            if j < 0:
                return "".join(out), True, opened
            i, inside = j + 3, False
        else:
            j = line.find("<!--", i)
            while j >= 0:   # 인라인 코드 안의 '<!--'는 글자 그대로다
                ticks, seen = ticks + line.count("`", seen, j), j
                if ticks % 2 == 0:
                    break
                j = line.find("<!--", j + 4)
            if j < 0 or (line.find("-->", j + 4) < 0 and line[:j].strip() and not closes_later):
                out.append(line[i:])
                return "".join(out), False, opened
            out.append(line[i:j])
            i, inside, opened = j + 4, True, opened + 1


def parse(text):
    """본문 블록(문단, 목록 항목), 제목, 본문에서 뺀 것의 수, 경고를 돌려준다.

    YAML·TOML 머리말, 코드 블록, 표, 인용문(>), 수식 블록, HTML 주석, 각주·링크 정의는 뺀다.
    """
    text = unicodedata.normalize("NFC", text.replace("\r\n", "\n").replace("\r", "\n"))   # 풀어쓴 자모를 합친다
    lines = PUA_RE.sub(" ", ZERO_WIDTH.sub("", text)).split("\n")   # 쪽 나눔 문자 등은 줄을 나누지 않는다
    skipped, warnings = Counter(), []
    start = 0
    if lines and lines[0].strip() in ("---", "+++"):
        mark_line = lines[0].strip()
        key = FRONT_KEY if mark_line == "---" else TOML_KEY
        for j in range(1, min(len(lines), 200)):
            if lines[j].strip() == mark_line or (mark_line == "---" and lines[j].strip() == "..."):
                if any(key.match(x) for x in lines[1:j]):
                    start = j + 1
                    skipped["머리말"] += 1
                break
    table = table_rows(lines)
    blocks, headings = [], []
    state = {"cur": None, "skip": None, "skip_line": 0, "depth": 0, "list": False,
             "comment": 0, "note": False, "note_gap": False}

    def flush():
        cur = state["cur"]
        if cur:
            nos = [no for no, _ in cur["parts"]]
            marked = "".join(f" {chr(PUA0 + min(k, PUA_MAX))} {txt}" for k, (_, txt) in enumerate(cur["parts"]))
            fmt_marked = strip_inline(marked)
            fmt, fstarts = unmark(fmt_marked, nos)
            body, starts = unmark(plain(fmt_marked), nos)
            if body or fmt:
                blocks.append({"type": cur["type"], "line": cur["line"], "nlines": len(cur["parts"]), "fmt": fmt,
                               "fstarts": fstarts, "text": body, "starts": starts})
        state["cur"] = None

    def begin_skip(kind, closer, no, label):
        flush()
        state["skip"], state["skip_line"] = (kind, closer), no
        skipped[label] += 1

    for i in range(start, len(lines)):
        line, no = lines[i], i + 1
        if state["skip"]:
            kind, closer = state["skip"]
            if kind == "fence":
                m = FENCE.match(line)
                if m and m.group(1)[0] == closer[0] and len(m.group(1)) >= closer[1] and not m.group(2).strip():
                    state["skip"] = None
            elif kind == "env":   # \begin ... \end 는 겹칠 수 있다
                state["depth"] += line.count("\\begin{") - line.count("\\end{")
                if state["depth"] <= 0:
                    state["skip"] = None
            elif closer.search(line):
                state["skip"] = None
            continue
        if state["comment"] or "<!--" in line:   # 주석만 걷어 내고 같은 줄의 나머지 글은 살린다
            later = any("-->" in x for x in lines[i + 1:i + 201])
            line, still, opened = cut_comments(line, bool(state["comment"]), later)
            if opened:
                skipped["주석"] += opened
            if still and not state["comment"]:
                state["comment"] = no
            elif not still:
                state["comment"] = 0
        s = line.strip()
        m = FENCE.match(line)
        if m:
            begin_skip("fence", (m.group(1)[0], len(m.group(1))), no, "코드 블록")
            continue
        if state["note"]:   # 각주 정의에 이어진 줄: 바로 다음 줄들, 빈 줄 뒤에는 들여쓴 줄만
            if not s:
                state["note_gap"] = True
                continue
            if not state["note_gap"] or INDENTED.match(line):
                continue
            state["note"] = False
        if not s:
            flush()
            continue
        if s.startswith("$$") or s.startswith("\\["):
            closer = "$$" if s.startswith("$$") else "\\]"
            if closer in s[2:]:
                flush()
                skipped["수식 블록"] += 1
            else:
                begin_skip("math", re.compile(re.escape(closer)), no, "수식 블록")
            continue
        if s.startswith("\\begin{"):
            depth = s.count("\\begin{") - s.count("\\end{")
            if depth <= 0:
                flush()
                skipped["수식 블록"] += 1
            else:
                begin_skip("env", None, no, "수식 블록")
                state["depth"] = depth
            continue
        raw = RAW_OPEN.match(line)
        if raw and not re.search(r"</%s\s*>" % raw.group(1), line[raw.end():], re.I):
            begin_skip("html", re.compile(r"</%s\s*>" % raw.group(1), re.I), no, "HTML 코드")
            continue
        if table[i]:
            flush()
            skipped["표(줄)"] += 1
            continue
        if QUOTE.match(line):
            flush()
            skipped["인용문(줄)"] += 1
            continue
        if REF_DEF.match(line):
            flush()
            skipped["각주·링크 정의"] += 1
            state["note"], state["note_gap"] = bool(FOOTNOTE_DEF.match(line)), False
            continue
        cur = state["cur"]
        li = LIST_ITEM.match(line)
        # 들여쓴 코드: 빈 줄 뒤, 목록 밖, 네 칸 이상 들여쓰기, 한글이 적은 줄만 코드로 본다(들여쓴 한국어 문단은 본문)
        if cur is None and not li and not state["list"] and INDENTED.match(line) and hangul_share(s) < 0.3:
            skipped["들여쓴 코드(줄)"] += 1
            continue
        h = atx_heading(line)
        if h is not None:
            flush()
            state["list"] = False
            headings.append((no, plain(strip_inline(h))))
            continue
        if cur and cur["type"] == "para" and (
                SETEXT_EQ.match(line) or (SETEXT_DASH.match(line) and len(cur["parts"]) == 1)):
            headings.append((cur["line"], plain(strip_inline(" ".join(t for _, t in cur["parts"])))))
            state["cur"] = None
            continue
        if HRULE.match(line):
            flush()
            continue
        if li:
            flush()
            state["list"] = True
            state["cur"] = {"type": "item", "line": no, "parts": [(no, line[li.end():].strip())]}
        elif cur is None:
            if not INDENTED.match(line) and not line.startswith("  "):
                state["list"] = False
            state["cur"] = {"type": "para", "line": no, "parts": [(no, s)]}
        else:
            cur["parts"].append((no, s))   # 같은 문단 안의 줄바꿈은 이어 붙인다
    flush()
    opened = None
    if state["skip"]:
        name = {"fence": "코드 블록이", "math": "수식 블록이", "env": "수식 블록이", "html": "HTML 코드가"}[state["skip"][0]]
        opened = (state["skip_line"], name)
    elif state["comment"]:
        opened = (state["comment"], "HTML 주석이")
    if opened:
        warnings.append(f"{opened[0]}행에서 연 {opened[1]} 닫히지 않아 그 뒤 {len(lines) - opened[0]}줄을 "
                        "본문에서 뺐습니다. 닫는 표시가 빠졌는지 확인하세요.")
    return blocks, headings, skipped, warnings


def strip_tail_cites(s):
    """문장 끝에 붙은 괄호·대괄호 덩어리(인용 번호, 출처 표기)를 떼어 낸다. 끝의 문장부호는 남긴다.

    뒤에서부터 한 번만 훑는다(괄호가 수천 개 이어진 입력에서도 느려지지 않게). 300자를 넘는 괄호는 인용으로 보지 않는다.
    """
    end = len(rtrim(s, TAIL_CHARS))
    i = end
    while True:
        j = i
        while j > 0 and s[j - 1].isspace():
            j -= 1
        if j > 0 and s[j - 1] == ")":
            depth, k = 0, j - 1
            while k >= 0 and j - k <= 300:
                if s[k] == ")":
                    depth += 1
                elif s[k] == "(":
                    depth -= 1
                    if depth == 0:
                        break
                k -= 1
            if k < 0 or j - k > 300 or depth != 0:
                break
            i = k
        elif j > 0 and s[j - 1] == "]":
            k = s.rfind("[", max(0, j - 300), j - 1)
            if k < 0 or "]" in s[k + 1:j - 1]:
                break
            i = k
        else:
            break
    return s[:i].rstrip() + s[end:] if i < end else s


def open_marks(s):
    need = [c for o, c in PAIRS if s.count(o) > s.count(c)]
    if s.count('"') % 2:
        need.append('"')
    return need


def rejoin(parts):
    """괄호나 따옴표가 열린 채 끊긴 조각을, 모두 닫히는 조각까지 다시 붙인다(인용 안에 문장이 여럿일 때).

    여덟 조각이나 400자 안에서 닫히지 않으면 짝 없는 표시로 보고 그대로 둔다.
    """
    out, i = [], 0
    while i < len(parts):
        cur = parts[i]
        if open_marks(cur):
            joined, j = cur, i + 1
            while j < len(parts) and j - i <= 8 and len(joined) < 400:
                joined = joined + " " + parts[j]
                if not open_marks(joined):
                    cur, i = joined, j
                    break
                j += 1
        out.append(cur)
        i += 1
    return out


def sentence_pieces(t):
    """문장 끝 표시(. ! ? …) 뒤에 닫는 따옴표·괄호가 오고 그다음이 공백이나 글 끝인 자리에서 자른다.

    앞에서부터 한 번만 훑는다(문장부호가 수천 개 이어진 글에서도 느려지지 않게).
    """
    n, p = len(t), 0
    while p < n:
        q, end = p + 1, n
        while q < n:
            if t[q] not in TERMINATORS:
                q += 1
                continue
            r = q
            while r < n and t[r] in TERMINATORS:
                r += 1
            c = r
            while c < n and t[c] in CLOSERS:
                c += 1
            if c == n or t[c].isspace():
                end = c
                break
            q = r
        yield t[p:end]
        p = end


def split_sentences(text):
    dots = lambda m: m.group(0).replace(".", DOT).replace("…", ELL)
    t = ABBR.sub(dots, text)
    t = DATE.sub(dots, t)
    t = ELLIPSIS_MID.sub(dots, t)
    nums = {int(m.group(1)) for m in ENUM.finditer(t)}   # '1. 수집 2. 정제'처럼 문장 안에서 이어지는 번호
    if nums:
        t = ENUM.sub(lambda m: m.group(1) + (DOT if int(m.group(1)) - 1 in nums or int(m.group(1)) + 1 in nums else "."), t)
    t = re.sub(r"(?<=[가-힣][.!?])(?=[가-힣])", " ", t)
    parts = rejoin([s for s in (piece.strip() for piece in sentence_pieces(t)) if s])
    return [s.replace(DOT, ".").replace(ELL, "…") for s in parts]


def lang_of(s):
    """한글이 있고 한국어 어절로 끝나면 한국어 문장으로 본다(영어 용어가 많거나 끝에 영문 인용이 붙어도)."""
    core = strip_tail_cites(s) or s
    h, l = len(HANGUL.findall(core)), len(LATIN.findall(core))
    if h == 0:
        return "en" if l >= 2 else None
    words = re.findall(r"[가-힣A-Za-z]+", core)
    return "ko" if l <= h or HANGUL.search(words[-1]) else "en"


def is_label(block, tagged):
    """마침표 없이 끝난 짧은 한 줄 문단(굵은 글씨 줄, 그림 줄, 캡션)은 제목처럼 본다.

    두 줄 이상에 걸친 문단, 세 어절 이상이면서 서술어로 끝난 줄('현장 접수는 받지 않습니다')은 문장이다.
    """
    text = block["text"]
    if block["nlines"] != 1:
        return False
    if CAPTION.match(text) and len(text) <= 100:
        return True
    if len(text) > LABEL_MAX or any(ENDED.search(s) for s, _ in tagged) or VERBAL_COLON.search(text):
        return False
    return not (len(text.split()) >= 3 and PREDICATE_END.search(text))


def analyze(text):
    blocks, headings, skipped, warnings = parse(text)
    ko, en, body, fragments, labels = [], [], [], 0, []
    for k, b in enumerate(blocks):
        tagged = [(s, lang_of(s)) for s in split_sentences(b["text"])]
        tagged = [(s, lang) for s, lang in tagged if lang]
        # 글머리의 제목 줄: 제목 표시(#) 없이 첫 줄에 쓴 제목은 서술어로 끝나도 제목이다('코드 리뷰는 언제부터 기다린 걸까')
        title = (k == 0 and len(blocks) >= 3 and b["type"] == "para" and b["nlines"] == 1 and len(b["text"]) <= LABEL_MAX
                 and not any(ENDED.search(s) for s, _ in tagged) and not (headings and headings[0][0] < b["line"]))
        if b["type"] == "para" and (title or is_label(b, tagged)):
            labels.append((b["line"], b["text"]))
            continue
        body.append(b)
        cursor = 0
        for s, lang in tagged:
            pos = b["text"].find(s[:8], cursor)
            pos = cursor if pos < 0 else pos
            cursor = pos + max(1, len(s) - 4)   # 다음 문장은 이 문장이 끝난 뒤에서 찾는다
            if b["type"] == "item" and not ENDED.search(s):
                fragments += 1   # 마침표 없는 개조식 항목은 문장 통계에서 뺀다
                continue
            (ko if lang == "ko" else en).append((line_of(b["starts"], pos), s))
    return {"blocks": body, "headings": sorted(headings), "label_lines": labels, "ko": ko, "en": en,
            "fragments": fragments, "labels": len(labels), "skipped": skipped, "warnings": warnings,
            "lines": [(b["starts"], b["text"]) for b in body],
            "chars": sum(len(b["text"]) for b in body)}


# ============================================================
# 지표 계산
# ============================================================
def short(s, n=40):
    return s if len(s) <= n else s[:n] + "…"


def snippet(line, start, end, width=14):
    a, b = max(0, start - width), min(len(line), end + width)
    return ("…" if a > 0 else "") + line[a:b] + ("…" if b < len(line) else "")


def at(no):
    """줄 번호 하나를 scan이 받는 위치 표로 바꾼다."""
    return [(0, no)]


def scan(patterns, units, skip_quoted=False):
    """패턴이 나온 자리. 겹치는 일치는 한 번만 센다. skip_quoted면 따옴표 안(인용·언급)은 뺀다."""
    hits = []
    for starts, line in units:
        quoted = [(q.start(), q.end()) for q in QUOTED.finditer(line)] if skip_quoted else []
        spans = sorted((m.start(), m.end()) for p in patterns for m in p.finditer(line))
        last = -1
        for a, b in spans:
            if a < last or any(qa <= a and b <= qb for qa, qb in quoted):
                continue
            hits.append((line_of(starts, a), snippet(line, a, b)))
            last = b
    return hits


def has_comma(s):
    """문장에 쉼표가 있는가. 천 단위 쉼표와 짧은 인용·언급 안의 쉼표는 세지 않는다."""
    return bool(ANY_COMMA.search(QUOTED.sub(" ", THOUSANDS.sub("0", s))))


def outside_quotes(pattern, s):
    """패턴이 짧은 인용 밖에서 한 번이라도 나오는가."""
    quoted = [(q.start(), q.end()) for q in QUOTED.finditer(s)]
    return any(not any(qa <= m.start() and m.end() <= qb for qa, qb in quoted) for m in pattern.finditer(s))


def conn_comma_hits(units):
    """연결어미·접속어 뒤 쉼표가 나온 자리. 짧은 따옴표 구간(인용·언급) 안의 쉼표는 뺀다."""
    hits = []
    for starts, line in units:
        quoted = [(q.start(), q.end()) for q in QUOTED.finditer(line)]

        def inside(end):   # end: 쉼표 바로 뒤 위치
            return any(qa < end <= qb - 1 for qa, qb in quoted)

        found = {m.end(): m.start() for m in PHRASE_COMMA.finditer(line) if not inside(m.end())}   # 쉼표 위치로 겹침을 막는다
        for m in WORD_COMMA.finditer(line):
            w = m.group(1)
            if m.end() in found or inside(m.end()):
                continue
            if w in CONN_ADV or w in CONN_WORDS:
                pass
            elif len(w) < 2 or not w.endswith(CONN_TAILS) or w.endswith(GO_NOUNS):
                continue
            elif len(w) > 2 and w.endswith(GO_COMPOUND):
                continue
            elif w in GO_AMBIG and not PARTICLE_BEFORE.search(line[:m.start()]):
                continue
            found[m.end()] = m.start()
        hits += [(line_of(starts, a), snippet(line, a, b)) for b, a in sorted(found.items())]
    return hits


def jeok_noun(w):
    """'적'으로 끝나지만 '-적(的)' 말이 아닌 명사인가."""
    if w.endswith(JEOK_TAILS) or w in JEOK_COMPOUNDS:
        return True
    if w.endswith(JEOK_NOUNS):
        return len(w) == 2 or (len(w) >= 4 and w[0] not in JEOK_PREFIX)
    return False


def jeok_hits(units):
    hits = []
    for starts, line in units:
        quoted = [(q.start(), q.end()) for q in QUOTED.finditer(line)]
        for m in JEOK.finditer(line):
            if jeok_noun(m.group(1)) or m.group(0).endswith(JEOK_ADVERBS):
                continue
            if any(qa <= m.start() and m.end() <= qb for qa, qb in quoted):
                continue
            hits.append((line_of(starts, m.start()), snippet(line, m.start(), m.end())))
    return hits


def end_key(s):
    """끝맺음 열쇠. 합니다체는 앞 음절까지('있습니다', '합니다'), 그 밖은 끝 2음절('했다', '어요')."""
    words = rtrim(strip_tail_cites(s), TRAIL_CHARS).split()
    runs = re.findall(r"[가-힣]+", words[-1]) if words else []
    if not runs:
        return None
    w = runs[-1]
    return w[-4:] if w.endswith("습니다") else w[-3:] if w.endswith("니다") else w[-2:]


def is_title_case(h):
    words = re.findall(r"[A-Za-z][A-Za-z'\-]*", h)
    main = [w for w in words if w.lower() not in SMALL_WORDS]
    if len(words) < 3 or not main or HANGUL.search(h):
        return False
    return all(w[0].isupper() for w in main)


def is_gloss(t):
    """괄호 안이 영어 병기로 보이는가(저자·연도 인용은 아니다)."""
    if PAREN_CITE.search(t):
        return False
    return t.isupper() if len(t) <= 2 else bool(re.search(r"[A-Z ]", t))


def compute(doc, genre="general"):
    """기준값과 무관한 원자료. {키: {"v": 값, "n": 횟수, "ex": 예시, "skip": 생략 이유}} 와 참고 정보."""
    ko, en, units, chars = doc["ko"], doc["en"], doc["lines"], doc["chars"]
    k = 1000 / chars if chars else 0.0
    few = None if len(ko) >= MIN_SENT else f"한국어 문장 {len(ko)}개, {MIN_SENT}개 미만"
    raw = {}

    def put(key, v, n=0, ex=None, skip=None, **more):
        raw[key] = dict({"v": v, "n": n, "ex": ex or [], "skip": skip}, **more)

    def ratio(key, picked):
        if few:
            put(key, None, skip=few)
        else:
            put(key, len(picked) / len(ko), len(picked), [(no, short(s)) for no, s in picked], total=len(ko))

    def count(key, hits):
        put(key, float(len(hits)), len(hits), hits)

    def density(key, hits):
        put(key, len(hits) * k, len(hits), hits)

    ratio("comma_ratio", [(no, s) for no, s in ko if has_comma(s)])
    density("conn_comma", conn_comma_hits(units))
    # 문장 길이와 끝맺음은 문장이 적으면 사람 글에서도 값이 크게 흔들려서 MIN_STYLE개 이상일 때만 잰다
    short_doc = None if len(ko) >= MIN_STYLE else f"한국어 문장 {len(ko)}개, {MIN_STYLE}개 미만"
    if short_doc:
        put("len_cv", None, skip=short_doc)
    else:
        lens = [len(re.sub(r"\s", "", s)) for _, s in ko]   # 한국어 문장만, 공백 제외 글자 수
        put("len_cv", statistics.pstdev(lens) / statistics.mean(lens), len(lens), mean=statistics.mean(lens))
    ends = [(no, s, end_key(s)) for no, s in ko]
    keys = [e for _, _, e in ends if e]
    if short_doc or len(keys) < MIN_STYLE:
        put("end_top", None, skip=short_doc or f"끝맺음을 읽은 문장 {len(keys)}개, {MIN_STYLE}개 미만")
    else:
        top, n = Counter(keys).most_common(1)[0]
        put("end_top", n / len(keys), n, [(no, short(s)) for no, s, e in ends if e == top], total=len(keys), top=top)
    own = [(no, s) for no, s in ko if not QUOTED.match(s.lstrip())]   # 따옴표 구간으로 시작한 문장의 첫말은 인용·언급이다
    ratio("opener_ratio", [(no, s) for no, s in own if OPENER_RE.match(s)])
    count("pivot", [(no, short(s, 30)) for no, s in own if PIVOT_RE.match(s)])
    count("pivot_other", [(no, short(s, 30)) for no, s in own if PIVOT_OTHER_RE.match(s)])
    density("deictic", [(no, short(s, 30)) for no, s in own if DEICTIC_RE.match(s)])
    ords = {}
    for no, s in own:
        m = ORDINAL_RE.match(s)
        if m:
            ords.setdefault(m.group(1) or m.group(2), no)
    count("ordinal", [(no, word) for word, no in ords.items()])
    density("dayanghan", scan(P_DAYANGHAN, units, True))
    density("preachy", scan(P_PREACHY, units, True))
    density("simply_not", scan(P_SIMPLY, units, True))
    density("through", scan(P_THROUGH, units, True))
    density("jeok", jeok_hits(units))
    density("can", scan(P_CAN, units, True))
    count("chatbot", scan(P_CHATBOT, units, True))
    for key, pats in P_NOTE.items():
        count(key, scan(pats, units, True))
    count("closing", [(no, short(s)) for no, s in ko[-3:] if outside_quotes(CLOSING[genre], s)])
    # 서식: 코드, 표, 인라인 코드는 이미 빠져 있다
    density("bold", scan([BOLD], [(b["fstarts"], b["fmt"]) for b in doc["blocks"]]))
    count("inline_header", [(b["line"], short(b["fmt"], 30)) for b in doc["blocks"]
                            if b["type"] == "item" and INLINE_HEADER.match(b["fmt"])])
    heads = [(at(no), h) for no, h in doc["headings"] + doc["label_lines"]]
    count("em_dash", scan([EM_DASH], units + heads, True))
    count("emoji", scan([EMOJI], units + heads))
    count("colon_heading", [(no, h) for no, h in doc["headings"] if re.search(r"[^\s:：][:：]\s+\S", h)])
    count("title_case", [(no, h) for no, h in doc["headings"] if is_title_case(h)])
    terms = Counter(m.group(1).strip() for _, line in units for m in PAREN_EN.finditer(line) if is_gloss(m.group(1).strip()))
    count("paren_en", [(0, f"{t} {n}회") for t, n in terms.items() if n >= 2])
    if len(en) >= 5 and len(en) >= 0.3 * (len(ko) + len(en)):   # 영어 문장이 꽤 있을 때만
        sents = [(at(no), s) for no, s in en]
        count("en_vocab", scan(EN_VOCAB, sents))
        count("en_pattern", scan(EN_PATTERN, sents))
    info = {"endings": Counter(keys).most_common(4), "end_div": None}
    if len(keys) >= WINDOW:
        info["end_div"] = statistics.mean(len(set(keys[i:i + WINDOW])) / WINDOW for i in range(len(keys) - WINDOW + 1))
    return raw, info


def near(v, limit, digits, pct=False):
    """값을 적는다. 기준과 똑같이 보이는데 실제로는 다르면 달라 보일 때까지 자릿수를 늘린다(55.2%와 기준 55%)."""
    for d in range(digits, digits + 5):
        spec = f".{d}%" if pct else f".{d}f"
        text = format(v, spec)
        if limit is None or v == limit or text != format(limit, spec):
            break
    return text


def show_value(key, r, limit=None):
    if r["v"] is None:
        return "생략"
    if key == "end_top":
        return f"{near(r['v'], limit, 0, True)} ({r['n']}/{r['total']}문장이 '{r['top']}'로 끝남)"
    if key in RATIO_KEYS:
        return f"{near(r['v'], limit, 0, True)} ({r['n']}/{r['total']}문장)"
    if key == "len_cv":
        return f"{near(r['v'], limit, 2)} (평균 {r['mean']:.0f}자)"
    if key in DENSITY_KEYS:
        return f"{r['n']}회 (1,000자당 {near(r['v'], limit, 2)})"
    return f"{r['n']}회"


def rule_text(key, mode, limit, least):
    if mode == "under":
        return f"{limit} 이상"
    if mode == "count":
        return "0회" if limit == 1 else f"{limit - 1}회 이하"
    base = f"{limit:.0%} 이하" if key in RATIO_KEYS else f"1,000자당 {limit} 이하"
    return base + (f"이거나 {least - 1}회 이하" if least > 1 else "")


def judge(raw, genre, chars):
    """원자료에 기준값을 댄다. state: flag(확인 필요) | pass(통과) | none(기준 없음) | skip(생략) | note(참고)."""
    th = dict(TH[genre], **TH_COMMON)
    items = []
    for key, label, mode, group in STRONG:
        r, t = raw[key], th.get(key)
        item = {"key": key, "label": label, "group": group, "value": r["v"], "show": show_value(key, r, t[0] if t else None),
                "ex": r["ex"], "skip": r["skip"], "rule": ""}
        if r["v"] is None:
            item["state"] = "skip"
        elif t is None:
            item["state"] = "none"
        else:
            limit, least = t
            if mode == "over":
                hit = r["v"] > limit and r["n"] >= least
            elif mode == "under":
                hit = r["v"] < limit
            else:
                hit = r["n"] >= limit
            item["state"] = "flag" if hit else "pass"
            item["rule"] = rule_text(key, mode, limit, least)
        items.append(item)

    def note(key, label):
        items.append({"key": key, "label": label, "group": None, "value": raw[key]["v"], "show": show_value(key, raw[key]),
                      "ex": raw[key]["ex"], "skip": None, "rule": "", "state": "note"})

    for key, (limit, least) in NOTE_TH[genre].items():
        if raw[key]["v"] > limit and raw[key]["n"] >= least:
            note(key, NOTE_LABEL[key])
    scale = max(1.0, chars / 2000)   # 긴 글에서는 참고 항목을 덜 띄운다
    for key, label, least, scaled in NOTES:
        if key in raw and raw[key]["n"] >= (math.ceil(least * scale) if scaled else least):
            note(key, label)
    if 1 <= raw["em_dash"]["n"] < th["em_dash"][0]:
        note("em_dash", "em dash(—) (문자 자체를 언급한 것이면 그대로 둔다)")
    return items


def measure(text, genre="general"):
    doc = analyze(text)
    raw, info = compute(doc, genre)
    items = judge(raw, genre, doc["chars"])
    kinds = sorted({i["group"] for i in items if i["state"] == "flag"})
    return {"doc": doc, "raw": raw, "info": info, "items": items, "kinds": kinds, "genre": genre}


# ============================================================
# 출력
# ============================================================
def report(res):
    doc, items, info = res["doc"], res["items"], res["info"]
    by = {s: [i for i in items if i["state"] == s] for s in ("flag", "note", "pass", "none", "skip")}
    head = f"분량 {doc['chars']:,}자(공백 포함), 한국어 문장 {len(doc['ko'])}개, 영어 문장 {len(doc['en'])}개"
    if doc["fragments"]:
        head += f", 마침표 없는 개조식 항목 {doc['fragments']}개"
    if doc["labels"]:
        head += f", 제목처럼 쓴 줄 {doc['labels']}개"
    if doc["fragments"] or doc["labels"]:
        head += "(문장 통계에서 제외)"
    out = [f"ai-tone-check v{VERSION} 측정 결과 ({GENRE_NAME[res['genre']]} 기준. 다시 볼 곳을 알려 주는 수치이며 판정이 아님)", head]
    if doc["skipped"]:
        out.append("본문에서 뺀 것: " + ", ".join(f"{k} {n}" for k, n in doc["skipped"].items()))
    out += ["주의: " + w for w in doc["warnings"]]
    if len(doc["ko"]) < MIN_SENT and doc["fragments"] + doc["labels"] >= MIN_SENT:
        out.append("마침표 없는 개조식 항목과 줄이 대부분이라 문장 단위 지표(쉼표, 문장 길이, 끝맺음, 문두 표지)는 생략합니다.")
    elif doc["chars"] < 800 or len(doc["ko"]) < MIN_SENT:
        out.append(f"짧은 글입니다. 기준값은 800자 이상, 한국어 문장 {MIN_SENT}개 이상인 글에 맞춘 것입니다.")

    def examples(i):
        rows = [f"    {str(no) + '행: ' if no else ''}{snip}" for no, snip in i["ex"][:MAX_EX]]
        if len(i["ex"]) > MAX_EX:
            rows.append(f"    외 {len(i['ex']) - MAX_EX}건")
        return rows

    kinds = res["kinds"]
    title = f"확인 필요 {len(by['flag'])}개"
    if len(kinds) != len(by["flag"]):
        title += f" (같은 습관을 두 번 잰 항목을 묶으면 {len(kinds)}가지: {', '.join(kinds)})"
    out += ["", title]
    for i in by["flag"]:
        out.append(f"- {i['label']}: {i['show']} (기준 {i['rule']})")
        out += examples(i)
    out += ["", f"참고 {len(by['note'])}개 (기준값 없이 나온 자리만 보여 줌. 읽고 판단하며 고칠 의무는 없음)"]
    for i in by["note"]:
        out.append(f"- {i['label']}: {i['show']}")
        out += examples(i)
    out += ["", f"통과 {len(by['pass'])}개"]
    out += [f"- {i['label']}: {i['show']} (기준 {i['rule']})" for i in by["pass"]]
    if by["none"]:
        out += ["", f"기준 없음 {len(by['none'])}개 (이 장르에서는 사람 글과 차이가 확인되지 않아 값만 보여 줌)"]
        out += [f"- {i['label']}: {i['show']}" for i in by["none"]]
    if by["skip"]:
        out += ["", f"생략 {len(by['skip'])}개"]
        out += [f"- {i['label']}: {i['skip']}" for i in by["skip"]]
    if info["endings"]:
        div = "" if info["end_div"] is None else f"{WINDOW}문장 안 끝맺음 종류 비율 {info['end_div']:.2f}. "
        out += ["", "끝맺음(참고 정보): " + div + "많이 쓴 끝: " + ", ".join(f"{e} {n}" for e, n in info["endings"])]
    return "\n".join(out)


# ============================================================
# 고치기 전후 비교
# ============================================================
def diff_words(wa, wb, spent=None):
    """(일치한 어절 수, 바뀐 구간 목록 또는 None).

    difflib과 같은 방식(가장 길게 겹친 구간을 찾고 그 앞뒤에서 다시 찾는다)으로 맞대되, 드는 일을 미리 셈해
    WORK_MAX를 넘으면 그만두고 어순을 무시한 어림값을 돌려준다. 같은 어절이 수백 번 되풀이되는 글에서는
    그대로 맞대면 몇 분이 걸린다. spent는 한 번의 비교에서 지금까지 쓴 일의 양을 담는 목록이다.
    """
    spent = [0] if spent is None else spent
    if wa == wb:
        return len(wa), []
    cb = Counter(wb)
    cost = [0]
    for w in wa:   # 원문 어절 하나를 고친 글의 같은 어절 모두와 맞대 보는 데 드는 일
        cost.append(cost[-1] + cb[w] + 1)
    sm = difflib.SequenceMatcher(None, wa, wb, autojunk=False)
    queue, blocks = [(0, len(wa), 0, len(wb))], []
    while queue:
        alo, ahi, blo, bhi = queue.pop()
        spent[0] += cost[ahi] - cost[alo]
        if spent[0] > WORK_MAX:
            return sum((Counter(wa) & cb).values()), None
        i, j, k = sm.find_longest_match(alo, ahi, blo, bhi)
        if k:
            blocks.append((i, j, k))
            if alo < i and blo < j:
                queue.append((alo, i, blo, j))
            if i + k < ahi and j + k < bhi:
                queue.append((i + k, ahi, j + k, bhi))
    ops, i, j, matched = [], 0, 0, 0
    for ai, bj, k in sorted(blocks) + [(len(wa), len(wb), 0)]:
        if i < ai or j < bj:
            ops.append(("replace" if i < ai and j < bj else "delete" if i < ai else "insert", i, ai, j, bj))
        i, j, matched = ai + k, bj + k, matched + k
    return matched, ops


def lost_and_new(pattern, a, b):
    ca, cb = Counter(pattern.findall(a)), Counter(pattern.findall(b))
    return sorted((ca - cb).elements()), sorted((cb - ca).elements())


def fact_tokens(words):
    """어절들에 든 숫자와 영문 표기를 나온 순서대로."""
    text = " ".join(words)
    return NUM_TOKEN.findall(text), LATIN_TOKEN.findall(text)


def words_and_ends(text):
    """어절 목록과, 문장이 끝나는 어절의 위치.

    문단, 목록 항목, 표의 줄, 제목이 끝나는 줄은 마침표가 없어도 경계로 본다. 문단 안에서 줄만 바꾼 곳은 경계가 아니다.
    """
    words, ends = [], set()
    lines = text.split("\n")
    for k, line in enumerate(lines):
        row = line.split()
        for w in row:
            if ENDED.search(w):
                ends.add(len(words))
            words.append(w)
        nxt = lines[k + 1] if k + 1 < len(lines) else ""
        if row and (not nxt.strip() or NEW_BLOCK.match(nxt) or ONE_LINE.match(line)):
            ends.add(len(words) - 1)
    return words, ends


def change_groups(wa, wb, ea, eb, ops):
    """바뀐 구간을 문장 단위로 묶고 그 끝까지 넓힌다. ea, eb는 문장이 끝나는 어절의 위치.

    돌려주는 값: [(a1, a2, b1, b2, runs_a, runs_b)]. 원문 어절 a1~a2가 고친 글 어절 b1~b2에 대응하고,
    그 안에서 실제로 바뀐 구간들이 runs_a, runs_b다.
    """
    merged = []
    for _, i1, i2, j1, j2 in ops:
        last = merged[-1] if merged else None
        if last and i1 - last[1] <= GAP_MAX and not any(k in ea for k in range(last[1], i1)):   # 같은 문장 안에서 또 바뀐 곳
            last[1], last[3] = i2, j2
            last[4].append((i1, i2))
            last[5].append((j1, j2))
        else:
            merged.append([i1, i2, j1, j2, [(i1, i2)], [(j1, j2)]])
    out = []
    for a1, a2, b1, b2, runs_a, runs_b in merged:
        n = 0
        while a1 > 0 and b1 > 0 and n < CONTEXT_MAX and not (a1 - 1 in ea and b1 - 1 in eb):
            a1, b1, n = a1 - 1, b1 - 1, n + 1
        n = 0
        while (a2 < len(wa) and b2 < len(wb) and n < CONTEXT_MAX
               and not ((a2 == 0 or a2 - 1 in ea) and (b2 == 0 or b2 - 1 in eb))):
            a2, b2, n = a2 + 1, b2 + 1, n + 1
        out.append((a1, a2, b1, b2, runs_a, runs_b))
    return out


def clip(words):
    """통째로 지우거나 넣은 글이 아주 길면 앞뒤 예순 어절씩만 보여 준다."""
    return words if len(words) <= LONG_RUN else words[:LONG_RUN // 2] + ["…"] + words[-(LONG_RUN // 2):]


def window(words, lo, hi, runs, around=8):
    """문장 [lo, hi)에서 바뀐 구간들(runs)을 앞뒤 여덟 어절과 함께 보여 준다.

    바뀐 어절은 모두 보여 주고, 바뀌지 않은 먼 곳과 통째로 바뀐 아주 긴 구간의 가운데만 '…'로 줄인다.
    """
    show = set()
    for s, e in runs:
        s = min(max(s, lo), hi)
        e = min(max(e, s), hi)
        show.update(range(max(lo, s - around), min(hi, e + around)))
        if e - s > LONG_RUN:
            show.difference_update(range(s + LONG_RUN // 2, e - LONG_RUN // 2))
    out, last = [], lo - 1
    for k in sorted(show):
        if k != last + 1:
            out.append("…")
        out.append(words[k])
        last = k
    if out and last != hi - 1:
        out.append("…")
    return " ".join(out) if out else "(없음)"


def spans(ends, lo, hi):
    """어절 [lo, hi)를 문장 단위 구간으로 나눈다."""
    out, s = [], lo
    for k in range(lo, hi):
        if k in ends:
            out.append((s, k + 1))
            s = k + 1
    if s < hi:
        out.append((s, hi))
    return out


def join_spans(words, parts):
    """떨어져 있는 문장들을 한 줄로 잇는다. 사이가 빈 곳은 '…'로 표시한다."""
    out, last = [], None
    for s, e in parts:
        if last is not None and s != last:
            out.append("…")
        out += words[s:e]
        last = e
    return " ".join(clip(out)) if out else "(없음)"


def gather(words, parts):
    """문장 구간들의 어절을 이어 붙인 목록과, 그 안에서 문장이 끝나는 위치."""
    out, ends = [], set()
    for s, e in parts:
        out += words[s:e]
        ends.add(len(out) - 1)
    return out, ends


def change_rows(wa, wb, ea, eb, ops, spent, nested=False):
    """바뀐 곳 목록과 자리를 옮긴 곳의 수.

    바뀐 곳은 (종류, 원문에서의 위치, 원문 쪽 글, 고친 쪽 글, 자리도 옮겼는지, 바뀐 어절 수).
    종류는 0 숫자·영문 표기가 바뀜, 1 그런 표기가 든 문장, 2 그 밖.
    바뀐 곳의 원문 쪽 문장이 고친 쪽(같은 곳이든 다른 곳이든)에 글자 그대로 있으면 자리만 옮긴 문장으로 보고 목록에서 뺀다.
    옮기면서 고친 문장은 원문 쪽과 고친 쪽을 한 줄로 묶어 보여 준다.
    """
    groups = change_groups(wa, wb, ea, eb, ops)
    olds = [spans(ea, g[0], g[1]) for g in groups]   # 바뀐 곳마다 원문 쪽 문장들
    news = [spans(eb, g[2], g[3]) for g in groups]   # 고친 쪽 문장들
    text_a = lambda q: " ".join(wa[q[0]:q[1]])
    text_b = lambda p: " ".join(wb[p[0]:p[1]])
    for old, new in zip(olds, news):   # 앞뒤에 딸려 온 똑같은 문장은 바뀐 것이 아니다(맞댄 자리가 한두 어절 밀린 경우)
        while old and new and text_a(old[0]) == text_b(new[0]):
            del old[0], new[0]
        while old and new and text_a(old[-1]) == text_b(new[-1]):
            del old[-1], new[-1]
    gone, came, links = set(), set(), {}   # 옮겨 간 원문 문장, 옮겨 온 고친 글 문장, {옮겨 온 곳: {떠난 곳: 문장 수}}

    def moved(d, q, i, p):
        gone.add((d, q))
        came.add((i, p))
        links.setdefault(i, Counter())[d] += 1

    size_a = lambda k: olds[k][-1][1] - olds[k][0][0] if olds[k] else 0
    size_b = lambda k: news[k][-1][1] - news[k][0][0] if news[k] else 0
    side_a = lambda k: " ".join(wa[olds[k][0][0]:olds[k][-1][1]])
    side_b = lambda k: " ".join(wb[news[k][0][0]:news[k][-1][1]])
    whole = {}   # 한쪽이 통째로 같은 경우. 두 어절 이하는 지우기만 한 곳과 넣기만 한 곳 사이에서만 본다
    for d in range(len(groups)):
        if size_a(d) >= 3 or (size_a(d) and not news[d]):
            whole.setdefault(side_a(d), []).append(d)
    for i in range(len(groups)):
        if size_b(i) >= 3 or (size_b(i) and not olds[i]):
            same = [d for d in whole.get(side_b(i), []) if d != i and len(olds[d]) == len(news[i])]
            if same:
                whole[side_b(i)].remove(same[0])
                for q, p in zip(olds[same[0]], news[i]):
                    moved(same[0], q, i, p)
    pool = {}
    for d, parts in enumerate(olds):
        for q in parts:
            if (d, q) not in gone:
                pool.setdefault(text_a(q), []).append((d, q))
    for i, parts in enumerate(news):
        for p in parts:
            if p[1] - p[0] < 3 or (i, p) in came:   # 두 어절 이하인 문장은 우연히 같을 수 있다
                continue
            same = pool.get(text_b(p), [])
            hit = next((x for x in same if x[0] != i), same[0] if same else None)   # 같은 곳 안에서 순서만 바뀐 문장도 옮긴 것이다
            if hit:
                same.remove(hit)
                moved(hit[0], hit[1], i, p)
    pair, taken = {}, set()
    for i, c in links.items():   # 옮겨 온 곳마다, 문장을 가장 많이 보내 준 곳 하나와 짝짓는다
        d = next((d for d, _ in c.most_common() if d not in taken), None)
        if d is not None:
            pair[i] = d
            taken.add(d)
    for i, d in pair.items():    # 짝지은 두 곳 사이에서는 짧은 문장도 같으면 옮긴 것이다
        left = {}
        for q in olds[d]:
            if (d, q) not in gone:
                left.setdefault(text_a(q), []).append(q)
        for p in news[i]:
            same = None if (i, p) in came else left.get(text_b(p))
            if same:
                gone.add((d, same.pop(0)))
                came.add((i, p))
    source = {d: i for i, d in pair.items()}   # 떠난 곳 → 옮겨 간 곳
    touched = {k for k, _ in gone} | {k for k, _ in came}
    left_a = lambda k: [q for q in olds[k] if (k, q) not in gone]
    left_b = lambda k: [p for p in news[k] if (k, p) not in came]
    places = len(links)
    rows, open_a, open_b = [], {}, {}   # open: 아직 짝을 찾지 못한 원문 쪽 / 고친 쪽 문장들 {바뀐 곳 번호: 문장들}

    def add(pos, words_a, words_b, show_a, show_b, shifted, size):
        ta, tb = fact_tokens(words_a), fact_tokens(words_b)
        rows.append((0 if ta != tb else 1 if any(ta) or any(tb) else 2, pos, show_a, show_b, shifted, size))

    def add_pair(ka, kb, must):
        """ka번째 곳의 원문 쪽 문장들과 kb번째 곳의 고친 쪽 문장들을 다시 맞대어, 바뀐 문장만 보여 준다.

        must가 아니면(글이 겹쳐서 짝 후보가 된 경우) 순서대로 맞대어 절반 이상이 같을 때만 묶는다. 묶었으면 True.
        """
        pa, pb, pos = open_a[ka], open_b[kb], groups[ka][0]
        (sub_a, ends_a), (sub_b, ends_b) = gather(wa, pa), gather(wb, pb)
        same, sub_ops = (0, None) if nested else diff_words(sub_a, sub_b, spent)
        if not must and (sub_ops is None or 4 * same < len(sub_a) + len(sub_b)):
            return False
        if sub_ops is None:
            add(pos, sub_a, sub_b, join_spans(wa, pa), join_spans(wb, pb), ka != kb, len(sub_a) + len(sub_b))
        else:
            sub_rows, _ = change_rows(sub_a, sub_b, ends_a, ends_b, sub_ops, spent, nested=True)
            rows.extend((kind, pos, show_a, show_b, ka != kb, size) for kind, _, show_a, show_b, _, size in sub_rows)
        del open_a[ka], open_b[kb]
        return True

    for k, (a1, _, _, _, runs_a, runs_b) in enumerate(groups):
        la, lb = left_a(k), left_b(k)
        if la and lb and k not in touched:   # 제자리에서 고친 곳: 바뀐 어절 둘레만 보여 준다
            add(a1, wa[la[0][0]:la[-1][1]], wb[lb[0][0]:lb[-1][1]],
                window(wa, la[0][0], la[-1][1], runs_a), window(wb, lb[0][0], lb[-1][1], runs_b),
                False, sum(e - s for s, e in runs_a + runs_b))
            continue
        if la:
            open_a[k] = la
        if lb:
            open_b[k] = lb
    # 남은 문장끼리 짝짓는다. 제자리의 것, 문장을 옮겨 보낸 곳의 것과는 그대로 묶고(tied),
    # 그 밖의 곳과는 어절의 60% 이상이 겹칠 때만 '옮기면서 고친 것'으로 묶는다. 많이 겹치는 짝부터 정한다
    wide = not nested and len(open_a) * len(open_b) <= 2500
    bags_a = {k: Counter(gather(wa, pa)[0]) for k, pa in open_a.items()}
    bags_b = {k: Counter(gather(wb, pb)[0]) for k, pb in open_b.items()}
    close = []
    for ka, bag_a in bags_a.items():
        for kb in (list(open_b) if wide else [k for k in {ka, source.get(ka)} if k in open_b]):
            tied = kb in (ka, source.get(ka))
            na, nb = sum(bag_a.values()), sum(bags_b[kb].values())
            same = sum((bag_a & bags_b[kb]).values())
            if tied or (min(na, nb) >= 4 and 10 * same >= 3 * (na + nb)):
                close.append((same / (na + nb) + (0.1 if tied else 0), -abs(ka - kb), ka, kb, tied))
    for _, _, ka, kb, tied in sorted(close, reverse=True):
        if ka in open_a and kb in open_b and add_pair(ka, kb, tied) and ka != kb and kb not in links:
            places += 1
    for k, pa in open_a.items():
        words = gather(wa, pa)[0]
        add(groups[k][0], words, [], join_spans(wa, pa), "(없음)", False, len(words))
    for k, pb in open_b.items():
        words = gather(wb, pb)[0]
        add(groups[k][0], [], words, "(없음)", join_spans(wb, pb), False, len(words))
    rows.sort(key=lambda r: r[:2])
    return rows, places


def compare_report(before, after):
    (wa, ea), (wb, eb) = words_and_ends(before), words_and_ends(after)
    total = len(wa) + len(wb)
    spent = [0]
    matched, ops = diff_words(wa, wb, spent)
    changed = total - 2 * matched
    pct = round(100 * changed / total) if total else 0
    out = []
    if wa and not wb:
        out.append("고친 글이 비어 있습니다. 원문 전체가 지워졌습니다.")
    rows, places = change_rows(wa, wb, ea, eb, ops, spent) if ops is not None else (None, 0)
    if ops is None and 10 * changed > 3 * total:
        # 어순을 무시하고 센 값은 제대로 맞댄 값보다 클 수 없다. 이것이 30%를 넘으면 실제로도 넘는다
        out.append(f"변경률(어절 단위): {pct}% 이상 (30% 초과. 글이 길거나 되풀이가 많아 어순을 무시하고 센 값)")
    elif ops is None:
        out.append(f"변경률(어절 단위): 약 {pct}% (글이 길거나 되풀이가 많아 어순을 무시하고 어림한 값. "
                   "순서만 바꾼 것은 드러나지 않아 실제는 더 클 수 있음. 30% 판정은 하지 않음)")
    else:
        verdict = lambda n: "30% 초과" if 10 * n > 3 * total else "30% 이하"   # 정수로 비교한다
        out.append(f"변경률(어절 단위): {pct}% ({verdict(changed)})")
        if places:
            kept = min(changed, sum(r[5] for r in rows))   # 옮긴 문장을 빼고, 목록에 남은 곳에서 바뀐 어절
            out.append(f"자리를 옮긴 곳 {places}곳이 변경률에 들어 있습니다. "
                       f"이를 빼면 {round(100 * kept / total)}%({verdict(kept)})입니다.")
    for name, pattern in (("숫자", NUM_TOKEN), ("영문 표기", LATIN_TOKEN)):
        lost, new = lost_and_new(pattern, before, after)
        if lost or new:
            out.append(f"바뀐 {name}: 사라짐 [{', '.join(lost[:12]) or '없음'}] / 새로 생김 [{', '.join(new[:12]) or '없음'}]")
        else:
            out.append(f"바뀐 {name}: 없음")
    if rows is None:
        out.append("바뀐 곳 목록은 글이 길거나 되풀이가 많아 생략했습니다. 고친 문단을 원문과 직접 대조하세요.")
    elif not rows:
        out.append("바뀐 곳: 없음" + (" (자리를 옮긴 곳 제외)" if places else ""))
    else:
        n = [sum(1 for r in rows if r[0] == k) for k in (0, 1, 2)]
        out.append(f"바뀐 곳 {len(rows)}곳: 숫자·영문 표기가 바뀐 곳 {n[0]}, 숫자·영문 표기가 든 문장 {n[1]}, 그 밖 {n[2]}")
        out.append("원문과 나란히 읽으세요. 수치의 대상과 단위, 정의, 조건, 주체, 부정이 달라졌으면 되돌립니다.")
        names = ("표기 바뀜", "숫자·표기 든 문장", "그 밖")
        for kind, _, ta, tb, shifted, _ in rows[:SHOW_MAX]:
            out.append(f'  [{names[kind]}] "{ta}"')
            out.append(f'      → "{tb}"' + (" (자리도 옮김)" if shifted else ""))
        if len(rows) > SHOW_MAX:
            more = rows[SHOW_MAX:]
            out.append(f"  외 {len(more)}곳(" + ", ".join(f"{names[k]} {sum(1 for r in more if r[0] == k)}" for k in (0, 1, 2)
                                                         if any(r[0] == k for r in more)) + ")은 직접 대조하세요.")
    pa, pb = (len([p for p in re.split(r"\n\s*\n", t.strip()) if p.strip()]) for t in (before, after))
    out.append(f"문단 수: {pa} → {pb}")
    out.append("자동으로 대조한 것은 숫자·영문 표기·문단 수뿐입니다. 뜻이 그대로인지는 바뀐 곳을 읽어 확인하세요.")
    return "\n".join(out)


def store_dir():
    """기준본과 임시 초안을 두는 사용자 전용 폴더. 이 도구가 만든 오래된 파일만 치운다."""
    uid = os.getuid() if hasattr(os, "getuid") else None   # 윈도우의 임시 폴더는 이미 사용자별이다
    folder = os.path.join(tempfile.gettempdir(), "ai-tone-check" if uid is None else f"ai-tone-check-{uid}")
    try:
        os.mkdir(folder, 0o700)
    except FileExistsError:
        pass
    except OSError as e:
        sys.exit(f"임시 폴더를 만들 수 없습니다: {folder} ({e.strerror})")
    if uid is not None:   # 여럿이 함께 쓰는 /tmp에서 남이 미리 만들어 둔 폴더나 링크는 쓰지 않는다
        st = os.lstat(folder)
        if not stat.S_ISDIR(st.st_mode) or st.st_uid != uid:
            sys.exit(f"임시 폴더를 쓸 수 없습니다. 다른 사용자의 것이거나 링크입니다: {folder}")
        if st.st_mode & 0o077:
            os.chmod(folder, 0o700)
    limit = time.time() - KEEP_DAYS * 86400
    try:
        for name in os.listdir(folder):
            path = os.path.join(folder, name)
            if OWN_FILE.match(name) and not os.path.islink(path) and os.path.isfile(path) and os.path.getmtime(path) < limit:
                os.remove(path)
    except OSError:
        pass
    return folder


def snapshot_path(path):
    key = hashlib.sha1(os.fsencode(os.path.normcase(os.path.abspath(path)))).hexdigest()[:16]
    return os.path.join(store_dir(), key + ".txt")


def save_snapshot(snap, text):
    fd, tmp = tempfile.mkstemp(dir=os.path.dirname(snap), prefix=".tmp-")   # 겹치지 않는 이름, 나만 읽는 권한
    try:
        with os.fdopen(fd, "wb") as f:   # 줄바꿈까지 그대로 남긴다
            f.write(text.encode("utf-8"))
        os.replace(tmp, snap)
    except OSError as e:
        try:
            os.remove(tmp)
        except OSError:
            pass
        sys.exit(f"기준본을 저장하지 못했습니다: {e.strerror}")


def is_scratch(path):
    """--scratch가 알려 준 임시 초안인가."""
    full = os.path.abspath(path)
    return (os.path.normcase(os.path.dirname(full)) == os.path.normcase(os.path.abspath(store_dir()))
            and bool(DRAFT_FILE.match(os.path.basename(full))))


def age_text(seconds):
    if seconds < 90:
        return "방금"
    if seconds < 5400:
        return f"{round(seconds / 60)}분 전"
    if seconds < 129600:
        return f"{round(seconds / 3600)}시간 전"
    return f"{round(seconds / 86400)}일 전"


def output_closed(err, fd=None, windows=None):
    """출력을 받던 쪽이 먼저 닫혀서 난 오류인가('| head' 따위).

    리눅스와 macOS는 BrokenPipeError를 낸다. 윈도우는 닫힌 파이프에 쓰면 OSError [Errno 22](EINVAL)를 낸다.
    EINVAL은 일반 파일에 쓰지 못했을 때처럼 다른 까닭으로도 나므로, 표준출력이 파이프일 때만 끊긴 것으로 본다.
    """
    if isinstance(err, BrokenPipeError):
        return True
    if windows is None:
        windows = os.name == "nt"
    if not windows or err.errno != errno.EINVAL:
        return False
    try:
        return stat.S_ISFIFO(os.fstat(sys.stdout.fileno() if fd is None else fd).st_mode)
    except (OSError, ValueError, AttributeError):
        return False


def say(text, end="\n"):
    """표준출력에 쓰고 바로 비운다. 출력을 받던 쪽이 먼저 닫혔으면 할 일은 끝났으므로 조용히 넘어간다.

    오류는 쓰고 비우는 이 자리에서만 받는다. 다른 자리에서 난 오류는 그대로 낸다.
    """
    try:
        sys.stdout.write(text + end)
        sys.stdout.flush()
    except OSError as err:
        if not output_closed(err):
            raise
        try:   # 남은 출력은 버린다. 파이썬이 끝날 때 다시 비우다가 같은 오류를 내지 않게 한다
            os.dup2(os.open(os.devnull, os.O_WRONLY), sys.stdout.fileno())
        except (OSError, ValueError, AttributeError):
            pass


class Parser(argparse.ArgumentParser):
    """도움말(-h, --help)도 say()로 내보내는 인자 해석기. 잘못된 인자의 사용법과 오류는 argparse대로 표준오류로 낸다."""

    def print_help(self, file=None):
        if file is None:
            say(self.format_help(), end="")
        else:
            super().print_help(file)


def main():
    for stream in (sys.stdout, sys.stderr):   # 윈도우 셸에서도 한글이 깨지지 않게
        try:
            stream.reconfigure(encoding="utf-8", errors="backslashreplace")
        except (AttributeError, ValueError):
            pass
    ap = Parser(description="긴 한국어 글의 AI 말투 지표를 잰다.")
    ap.add_argument("path", nargs="?", help="측정할 파일")
    ap.add_argument("--genre", choices=sorted(TH), default="general", help="general(기본) 또는 academic(논문·초록)")
    ap.add_argument("--mark", action="store_true", help="지금 내용을 비교 기준본으로 저장")
    ap.add_argument("--reset", action="store_true", help="--mark와 함께: 이미 있는 기준본을 지금 내용으로 바꾼다")
    ap.add_argument("--compare", action="store_true", help="저장해 둔 기준본과 비교")
    ap.add_argument("--forget", action="store_true", help="이 글의 기준본을 지운다(임시 초안이면 초안 파일도)")
    ap.add_argument("--diff", nargs=2, metavar=("BEFORE", "AFTER"), help="두 파일만 비교")
    ap.add_argument("--scratch", action="store_true", help="채팅용 글을 저장할 임시 파일 경로를 알려 준다")
    args = ap.parse_args()
    if args.scratch:
        say(os.path.join(store_dir(), f"draft-{time.strftime('%Y%m%d-%H%M%S')}-{os.getpid() % 1000:03d}.md"))
        return
    if args.diff:
        say(compare_report(read_text(args.diff[0]), read_text(args.diff[1])))
        return
    if not args.path:
        ap.error("파일 경로를 주세요.")
    if args.forget:   # 원고 파일이 이미 없어도 기준본은 지울 수 있어야 한다
        snap = snapshot_path(args.path)
        had_snap, draft = os.path.exists(snap), is_scratch(args.path) and os.path.isfile(args.path)
        if had_snap:
            os.remove(snap)
        if draft:   # 임시 초안은 초안 파일까지 지운다. 그 밖의 원고 파일은 건드리지 않는다
            os.remove(args.path)
        if had_snap and draft:
            say("이 글의 기준본과 임시 초안을 지웠습니다.")
        elif draft:
            say("임시 초안을 지웠습니다. 기준본은 없었습니다.")
        elif had_snap:
            say("이 글의 기준본을 지웠습니다. 원고 파일은 그대로 있습니다.")
        else:
            say("지울 기준본이 없습니다.")
        if draft or not (args.mark or args.compare):
            return
    text = read_text(args.path)
    empty = not text.strip()
    out = ["빈 글입니다. 측정할 내용이 없습니다." if empty else report(measure(text, args.genre))]
    if args.mark or args.compare:
        snap = snapshot_path(args.path)
        old = read_text(snap) if os.path.exists(snap) else None
        age = time.time() - os.path.getmtime(snap) if old is not None else 0
        if args.compare and old is None:
            out.append("\n기준본이 없습니다. 고치기 전에 --mark로 먼저 재야 비교할 수 있습니다.")
        elif args.compare:
            out.append(f"\n기준본과 비교 (기준본 저장: {age_text(age)})\n" + compare_report(old, text))
        if not args.mark:
            pass
        elif empty:
            out.append("\n빈 글이라 기준본으로 저장하지 않았습니다.")
        elif old is None or args.reset:
            save_snapshot(snap, text)
            out.append("\n지금 내용을 기준본으로 저장했습니다. 고친 뒤 --compare로 다시 재면 바뀐 정도를 알려 줍니다.")
        elif old == text:
            out.append(f"\n기준본이 이미 지금 내용과 같습니다(저장: {age_text(age)}).")
        elif age < KEEP_HOURS * 3600:
            out.append(f"\n{age_text(age)} 저장한 기준본이 있고 지금 내용과 달라서 그대로 두었습니다. "
                       "같은 작업 중이면 --compare로 비교하세요. 새 작업이라 기준본을 다시 잡으려면 --mark --reset을 쓰세요.")
        else:
            save_snapshot(snap, text)
            out.append(f"\n오래된 기준본({age_text(age)} 저장)을 지금 내용으로 바꿨습니다. 고친 뒤 --compare로 다시 재면 바뀐 정도를 알려 줍니다.")
    say("\n".join(out))   # 저장까지 마친 뒤 한 번에 내보낸다(출력이 도중에 끊겨도 기준본은 남는다)


if __name__ == "__main__":
    main()
