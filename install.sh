#!/bin/bash

npm install --save
git clone https://github.com/theme-next/hexo-theme-next themes/next
node_modules/hexo/bin/hexo generate
# node_modules/hexo/bin/hexo server
