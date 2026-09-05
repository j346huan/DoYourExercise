import type { NextConfig } from 'next';
const config: NextConfig = {
  output: 'export',
  trailingSlash: true,
  basePath: process.env.SITE_BASE_PATH || '',
  images: { unoptimized: true },
};
export default config;
