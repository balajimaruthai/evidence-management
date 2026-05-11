# camera.py

import cv2
import PIL.Image
from PIL import Image
class VideoCamera(object):
    def __init__(self):
       
        ff=open("file1.txt","r")
        file1=ff.read()
        ff.close()
        
        self.video = cv2.VideoCapture(file1)
        self.k=1
        
        
    
    def __del__(self):
        self.video.release()
        
    
    def get_frame(self):
        success, image = self.video.read()
      
            
        # We are using Motion JPEG, but OpenCV defaults to capture raw images,
        # so we must encode it into JPEG in order to correctly display the
        # video stream.
        ret, jpeg = cv2.imencode('.jpg', image)
        return jpeg.tobytes()
