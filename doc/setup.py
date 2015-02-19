from setuptools import setup
setup(
    name = "NetProveTermStyle",
    version = "0.1",
    packages = ['netprovetermstyle'],
    entry_points = '''
        [pygments.styles]
        netprovetermstyle = netprovetermstyle:NetProveTermStyle
    '''
)