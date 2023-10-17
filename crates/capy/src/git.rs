use std::{
    fs::{self, File},
    io::{BufWriter, Read, Write},
    path::Path,
};

use base64::{engine::general_purpose, Engine};
use reqwest::blocking::Client;
use serde_json::Value;

const GITHUB_URL: &str = "https://api.github.com/repos/capy-language/capy/contents";

pub(crate) fn download_core(lib_dir: &Path) {
    download_github_dir(lib_dir, "core");
}

/// based on [isurfer21/clone-github-subdir](https://github.com/isurfer21/clone-github-subdir)
pub(crate) fn download_github_dir(lib_dir: &Path, path: &str) {
    let client = Client::new();

    let mut response = client
        .get(&format!("{GITHUB_URL}/{path}"))
        .header("User-Agent", " ")
        .send()
        .expect("Failed to get response from capy-language/capy:core");

    let mut body = String::new();
    response
        .read_to_string(&mut body)
        .expect("Failed to read response of capy-language/capy:core");

    let item_list: Value =
        serde_json::from_str(&body).expect("Invalid response from capy-language/capy:core");
    if let Some(array) = item_list.as_array() {
        for element in array {
            let file_ty = element["type"]
                .as_str()
                .expect("no file type in the response items");
            match file_ty {
                "dir" => {
                    let dir_url = element["url"].as_str().expect("Invalud sub-directory URL");

                    download_github_dir(lib_dir, dir_url);
                }
                "file" => {
                    let file_path = element["path"]
                        .as_str()
                        .expect("Invalud filepath in the sub-directory");
                    let file_dir = Path::new(file_path)
                        .parent()
                        .as_ref()
                        .and_then(|p| p.to_str())
                        .expect("Invalid directory path of the file");

                    let file_url = element["download_url"]
                        .as_str()
                        .expect("Invalid download file URL");

                    download_file(file_url, &lib_dir.join(file_dir));
                }
                _ => {}
            }
        }
    } else if let Some(object) = item_list.as_object() {
        let file_type = object["type"]
            .as_str()
            .expect("No file type in the response");
        if file_type == "file" {
            let file_encoding = object["encoding"]
                .as_str()
                .expect("No file encoding scheme provided in response");
            if file_encoding == "base64" {
                let file_name = object["name"].as_str().unwrap();
                let file_content = object["content"].as_str().unwrap().replace('\n', "");
                let bytes = &general_purpose::STANDARD.decode(file_content).unwrap();
                fs::write(file_name, bytes).unwrap();
                println!(" {}", file_name);
            }
        }
    } else {
        panic!("Invalid response from GitHub API");
    }
}

fn download_file(url: &str, path: &Path) {
    let file_name = url.split('/').last().expect("Invalid download file URL");
    let client = Client::new();
    let response = client
        .get(url)
        .send()
        .expect("Failed to get response for file");

    fs::create_dir_all(path).expect("failed to create directory");

    let file_path = path.join(file_name);
    let file = File::create(file_path.clone()).expect("Failed to create file");
    let mut writer = BufWriter::new(file);

    std::io::copy(
        &mut response.bytes().expect("Failed to get bytes").as_ref(),
        &mut writer,
    )
    .expect("Failed to copy data");

    writer.flush().expect("Failed to flush writer");
}
