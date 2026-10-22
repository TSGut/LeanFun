"""Unit tests for the version string shown in the RevOLVER and its PDF."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import version  # noqa: E402


class VersionTests(unittest.TestCase):
    def test_format(self):
        self.assertEqual(version.format_version('v0.2.0', 0, 'a1b2c3d', False), 'v0.2.0')
        self.assertEqual(version.format_version('v0.2.0', 14, 'a1b2c3d', False), 'v0.2.0+14 (a1b2c3d)')
        self.assertEqual(version.format_version('v0.2.0', 0, 'a1b2c3d', True), 'v0.2.0 (a1b2c3d, modified)')
        self.assertEqual(version.format_version(None, 0, 'a1b2c3d', False), 'unreleased (a1b2c3d)')
        self.assertEqual(version.format_version(None, 0, 'a1b2c3d', True), 'unreleased (a1b2c3d, modified)')

    def test_url(self):
        repo = 'https://github.com/TSGut/LeanFun/'
        self.assertEqual(version.version_url(repo, 'v0.2.0', 0, 'f' * 40, False),
                         'https://github.com/TSGut/LeanFun/releases/tag/v0.2.0')
        self.assertEqual(version.version_url(repo, 'v0.2.0', 3, 'f' * 40, False),
                         'https://github.com/TSGut/LeanFun/commit/' + 'f' * 40)
        self.assertEqual(version.version_url(repo, None, 0, 'f' * 40, False),
                         'https://github.com/TSGut/LeanFun/commit/' + 'f' * 40)

    def test_current_checkout(self):
        tag, distance, short, full, dirty = version.describe()
        self.assertRegex(version.format_version(tag, distance, short, dirty),
                         r'^(v\d+\.\d+\.\d+|unreleased)')


if __name__ == '__main__':
    unittest.main()
