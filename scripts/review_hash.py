"""Versioned canonical graph hash; called by the Lean extractor, not a renderer."""
import hashlib
import json
import sys


def fingerprint(item):
    if item.get('missing'):
        return item
    records = sorted(item.pop('records'), key=lambda r: json.dumps(r['id'], ensure_ascii=True, separators=(',', ':')))
    payload = json.dumps({'version': 1, 'records': records},
                         ensure_ascii=True, sort_keys=True, separators=(',', ':'))
    item['fingerprint'] = hashlib.sha256(payload.encode('utf-8')).hexdigest()
    item['external'] = sorted(set(item['external']))
    return item


if __name__ == '__main__':
    print(json.dumps([fingerprint(item) for item in json.load(sys.stdin)], ensure_ascii=False))
