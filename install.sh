#!/bin/bash

npm install hexo

node_modules/hexo/bin/hexo init binary
cd binary
cp ../config/package.json package.json
npm install
git clone https://github.com/iissnan/hexo-theme-next themes/next
cp ../config/next.yml themes/next/_config.yml
cp ../config/site_settings.yml _config.yml
../node_modules/hexo/bin/hexo generate
# ../node_modules/hexo/bin/hexo server
