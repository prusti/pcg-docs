#!/usr/bin/env node

const { execSync } = require('child_process');
const fs = require('fs');
const path = require('path');

const MDBOOK_VERSION = '0.4.52';
const MDBOOK_KATEX_VERSION = '0.9.3';

function commandExists(command) {
  try {
    execSync(`which ${command}`, { stdio: 'ignore' });
    return true;
  } catch {
    return false;
  }
}

function getVersion(command, versionArg = '--version') {
  try {
    const output = execSync(`${command} ${versionArg}`, { encoding: 'utf-8' });
    const match = output.match(/(\d+\.\d+\.\d+)/);
    return match ? match[1] : null;
  } catch {
    return null;
  }
}

function installWithCargo(crate, version) {
  console.log(`Installing ${crate} v${version}...`);
  try {
    execSync(`cargo install --version ${version} ${crate}`, { stdio: 'inherit' });
    console.log(`✓ ${crate} v${version} installed successfully`);
  } catch (error) {
    console.error(`✗ Failed to install ${crate}: ${error.message}`);
    process.exit(1);
  }
}

function checkAndInstall(command, crate, targetVersion) {
  if (commandExists(command)) {
    const currentVersion = getVersion(command);
    if (currentVersion) {
      const current = currentVersion.split('.').map(Number);
      const target = targetVersion.split('.').map(Number);

      // Check if current version is compatible (same major.minor)
      if (current[0] === target[0] && current[1] === target[1]) {
        console.log(`✓ ${command} v${currentVersion} is installed and compatible`);
        return;
      } else {
        console.log(`⚠ ${command} v${currentVersion} is installed but may not be compatible`);
        console.log(`  Recommended version: v${targetVersion}`);
        console.log(`  To update: cargo install --force --version ${targetVersion} ${crate}`);
        return;
      }
    }
  }

  installWithCargo(crate, targetVersion);
}

function main() {
  console.log('🚀 Setting up mdbook and dependencies...\n');

  // Check if cargo is installed
  if (!commandExists('cargo')) {
    console.error('✗ Cargo (Rust) is not installed.');
    console.error('  Please install Rust from: https://www.rust-lang.org/tools/install');
    console.error('  Then run this setup again.');
    process.exit(1);
  }
  console.log('✓ Cargo is installed');

  // Check and install mdbook
  checkAndInstall('mdbook', 'mdbook', MDBOOK_VERSION);

  // Check and install mdbook-katex
  checkAndInstall('mdbook-katex', 'mdbook-katex', MDBOOK_KATEX_VERSION);

  console.log('\n✨ Setup complete! You can now run:');
  console.log('  npm run serve  - Start development server');
  console.log('  npm run build  - Build for production');
}

main();
