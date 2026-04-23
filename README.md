# Automatic Number Plate Recognition (ANPR) System

## 📌 Project Overview

This project implements an Automatic Number Plate Recognition (ANPR) system using YOLOv8.
It detects vehicles, extracts number plates, and recognizes characters from the plate.

---

## 🤖 Models Used

The trained YOLOv8 models are hosted on Hugging Face:

* Plate Detection Model:
  https://huggingface.co/workwithPujan/detect_plate.pt

* Character Recognition Model:
  https://huggingface.co/workwithPujan/detect_plate.pt

---

## 📥 Model Loading

The models are automatically downloaded using `huggingface_hub`:

```python
from ultralytics import YOLO
from huggingface_hub import hf_hub_download

repo_id = "workwithPujan/detect_plate.pt"

plate_model = YOLO(hf_hub_download(repo_id, "detect_plate.pt"))
text_model = YOLO(hf_hub_download(repo_id, "robo_best.pt"))
```

---

## ⚙️ Requirements

* Python 3.8+
* ultralytics
* huggingface_hub
* opencv-python
* reportlab
Install dependencies:

```bash
pip install ultralytics huggingface_hub opencv-python reportlab
```

---

## 🚀 How to Run

1. Clone the repository
2. Run the main script:

```bash
python main.py
'''

## 📊 Features

* Real-time vehicle detection
* Number plate localization
* Character recognition using YOLO
* High accuracy (mAP@50 ≈ 0.97–0.98)

## 📌 Note

Models are not stored in this GitHub repository due to large size.
They are hosted on Hugging Face and downloaded automatically during runtime.

---

## 👨‍💻 Author

Pujan Baniya
