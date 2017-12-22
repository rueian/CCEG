export function refreshPage() {
    location.reload();
}

export function handleAxiosError(error) {
    if (error.response) {
        // The request was made and the server responded with a status code
        // that falls out of the range of 2xx
        // console.log(error.response.data);
        // console.log(error.response.status);
        // console.log(error.response.headers);
        if (error.response.data.message) {
            alert('發送失敗: ' + error.response.data.message);
        } else if (error.response.data.error) {
            alert('發送失敗: ' + error.response.data.error);
        } else {
            alert('發送失敗: ' + JSON.stringify(error.response.data));
        }

        if (error.response.data.refresh) {
            window.location.reload();
        }

        return;
    } else if (error.request) {
        // The request was made but no response was received
        // `error.request` is an instance of XMLHttpRequest in the browser and an instance of
        // http.ClientRequest in node.js
        console.log(error.request);
    } else {
        // Something happened in setting up the request that triggered an Error
        console.log('Error', error.message);
    }
    console.log(error.config);
    alert('發送失敗，請稍後再試');
}